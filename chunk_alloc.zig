// packages
const std = @import("std");
const page_alloc = @import("page_alloc.zig");

// modules
const builtin = std.builtin;
const debug = std.debug;
const math = std.math;
const mem = std.mem;
const os = std.os;
const testing = std.testing;

// functions
const assert = debug.assert;

// types
const Mutex = std.Mutex;

// constants"
const page_size = mem.page_size;

pub const Error = error{OutOfMemory};

/// A page-aligned pointer to a chunk of `size` bytes
pub fn ChunkPointer(comptime size: usize) type {
    return *align(page_size) [size]u8;
}

/// A trait to determine if a type is a chunk allocator.
/// Chunk allocators must support the following decls:
///   T.chunk_size: const usize
///   T.allocChunk: const fn(*T) Error!ChunkPointer(T.chunk_size)
///   T.freeChunk: const fn(*T, [*]u8) void
pub fn isChunkAllocator(comptime T: type) bool {
    comptime {
        return @hasDecl(T, "chunk_size") and
            @TypeOf(T.chunk_size) == usize and
            @hasDecl(T, "allocChunk") and
            @TypeOf(T.allocChunk) == fn (*T) Error!ChunkPointer(T.chunk_size) and
            @hasDecl(T, "freeChunk") and
            @TypeOf(T.freeChunk) == fn (*T, [*]u8) void;
    }
}

/// Linked list data format for the free list of chunks.
/// Chunks in the free list can be reinterpreted as this.
pub const ChunkHeader = struct { next: ?*ChunkHeader };

/// An allocator that allocates large chunks from the operating system.
/// If the chunk size is smaller than the OS memory map granularity,
/// os allocations will be broken up into chunks and stored into a free list.
/// This allocator never decommits memory, it only grows.
pub fn ThreadsafeChunkAllocator(comptime in_chunk_size: usize) type {
    if (!math.isPowerOfTwo(in_chunk_size)) @compileError("Chunk size must be a power of two");
    if (in_chunk_size < page_size) @compileError("Chunk size must be greater than or equal to page size");
    return struct {
        /// The size of a chunk.  All chunks are exactly this size, with no waste.
        pub const chunk_size = in_chunk_size;

        /// A pointer to a data chunk of constant size
        pub const ChunkPtr = ChunkPointer(chunk_size);

        /// The granularity of direct allocation, as reported by the OS.
        /// This may be larger or smaller than the chunk size.
        /// It will always be greater than or equal to page_size.
        /// This value does not change after initialization.
        allocation_granularity_bytes: usize,

        /// Lock protecting mutable state
        /// Allocation and free from this allocator incurs locking cost.
        lock: Mutex,

        /// The total number of bytes that are currently in use.
        /// protected by lock
        total_in_use_bytes: usize,

        /// The total number of bytes that are currently in use.
        /// protected by lock
        total_free_list_bytes: usize,

        /// The head of a free list of chunks.
        /// Reinterpret chunks as ChunkHeader to follow list.
        /// protected by lock
        first_free_chunk: ?*ChunkHeader,

        /// Initialize a chunk allocator.  Queries the OS to get allocation granularity.
        /// This allocator is meant to be global and everlasting.  It cannot release
        /// virtual address space.  Once initialized, this allocator cannot be disposed.
        pub fn init() @This() {
            return @This(){
                .allocation_granularity_bytes = page_alloc.findAllocationGranularity(),
                .lock = Mutex.init(),
                .total_in_use_bytes = 0,
                .total_free_list_bytes = 0,
                .first_free_chunk = null,
            };
        }

        /// Adds freed chunks for the requested number of freed bytes to the allocator.
        /// Errors:
        ///   OutOfMemory -> No memory was seeded, the system is entirely out
        ///   PartialOutOfMemory -> Some memory was seeded but not as much as requested
        pub fn seed(self: *@This(), num_bytes: usize) (Error || error{PartialOutOfMemory})!void {
            assert(math.isPowerOfTwo(num_bytes));
            const granule_size = math.max(self.allocation_granularity_bytes, chunk_size);
            const actual_bytes = math.max(num_bytes, granule_size);

            var new_tail_chunk: ?*ChunkHeader = null;
            var new_head_chunk: ?*ChunkHeader = null;
            var remaining_bytes = actual_bytes;
            var allocation_size = actual_bytes;

            // Try to allocate the requested amount.  If an allocation fails,
            // try to make multiple smaller allocations.
            while (remaining_bytes > 0 and allocation_size >= granule_size) {
                if (page_alloc.alloc(allocation_size)) |new_bytes| {
                    // link the chunks together in the new allocation
                    const head = @ptrCast(*ChunkHeader, new_bytes);
                    var tail = head;
                    var offset = chunk_size;
                    while (offset < allocation_size) : (offset += chunk_size) {
                        const next_tail = @ptrCast(*ChunkHeader, @alignCast(page_size, new_bytes + offset));
                        tail.next = next_tail;
                        tail = next_tail;
                    }

                    // link into the larger list
                    if (new_tail_chunk == null) new_tail_chunk = tail;
                    tail.next = new_head_chunk;
                    new_head_chunk = head;

                    remaining_bytes -= allocation_size;
                } else |err| {
                    // try a smaller allocation
                    allocation_size = allocation_size / 2;
                }
            }

            // link the new chunks
            if (new_tail_chunk) |tail| {
                const locked = self.lock.acquire();
                defer locked.release();

                // link
                tail.next = self.first_free_chunk;
                self.first_free_chunk = new_head_chunk;

                // update stats
                self.total_free_list_bytes += actual_bytes - remaining_bytes;
            }

            if (remaining_bytes == 0) {
                return;
            } else if (remaining_bytes < actual_bytes) {
                return error.PartialOutOfMemory;
            } else {
                return error.OutOfMemory;
            }
        }

        /// Allocates and returns a single chunk.  If the free list is empty,
        /// attempts to alloc from the OS.
        pub fn allocChunk(self: *@This()) Error!ChunkPtr {
            // Fast path: see if we can grab an available free chunk
            {
                const locked = self.lock.acquire();
                defer locked.release();

                // claim bytes as in use.  If an error occurs
                // we will reset this at the end
                self.total_in_use_bytes += chunk_size;

                if (self.first_free_chunk) |chunk| {
                    // claim the bytes
                    self.total_free_list_bytes -= chunk_size;

                    // return a free chunk
                    self.first_free_chunk = chunk.next;
                    return @intToPtr(ChunkPtr, @ptrToInt(chunk));
                }
            }

            // No free chunk available.  Try to map.  Not locked here.
            if (self.mapNewChunk()) |chunk| {
                return chunk;
            } else |err| {
                assert(err == error.OutOfMemory);
                // try to quick alloc a chunk again, another thread may have
                // added more to the linked list
                const locked = self.lock.acquire();
                defer locked.release();
                if (self.first_free_chunk) |chunk| {
                    // claim the bytes
                    self.total_free_list_bytes -= chunk_size;

                    // return a free chunk
                    self.first_free_chunk = chunk.next;
                    return @intToPtr(ChunkPtr, @ptrToInt(chunk));
                }

                // couldn't get the bytes, unclaim them for stats
                self.total_in_use_bytes -= chunk_size;

                // otherwise no chunks left, return the error.
                return err;
            }
        }

        /// Maps and returns a new chunk.  If the allocation granularity is larger than the chunk size,
        /// adds extra chunks to the internal list.
        fn mapNewChunk(self: *@This()) Error!ChunkPtr {
            if (self.allocation_granularity_bytes > chunk_size) {
                // must be power of two chunks
                assert(self.allocation_granularity_bytes >= 2 * chunk_size);

                const new_chunks = try page_alloc.alloc(self.allocation_granularity_bytes);
                const first_chunk = @ptrCast(ChunkPtr, new_chunks);
                const second_chunk = @ptrCast(*ChunkHeader, @alignCast(page_size, new_chunks + chunk_size));

                // link all chunks starting at the second chunk together.
                // we don't need the lock because these chunks aren't published.
                var last_chunk = second_chunk;
                var offset = chunk_size + chunk_size;
                while (offset < self.allocation_granularity_bytes) : (offset += chunk_size) {
                    const next_chunk = @ptrCast(*ChunkHeader, @alignCast(page_size, new_chunks + offset));
                    last_chunk.next = next_chunk;
                    last_chunk = next_chunk;
                }

                const total_new_bytes: usize = offset - chunk_size;

                // link our prepared list into the actual list
                {
                    const locked = self.lock.acquire();
                    defer locked.release();

                    // update stats
                    self.total_free_list_bytes += total_new_bytes;
                    // total_in_use_bytes has already been updated by the caller

                    // link list
                    last_chunk.next = self.first_free_chunk;
                    self.first_free_chunk = second_chunk;
                }

                // return the first chunk
                return first_chunk;
            } else {
                const new_chunk = try page_alloc.alloc(chunk_size);
                return @ptrCast(ChunkPtr, new_chunk);
            }
        }

        /// Returns a chunk to the free list.  This chunk remains committed and available.
        pub fn freeChunk(self: *@This(), chunk_ptr: [*]u8) void {
            const chunk = @ptrCast(*ChunkHeader, @alignCast(page_size, chunk_ptr));
            {
                const locked = self.lock.acquire();
                defer locked.release();

                // update stats
                self.total_free_list_bytes += chunk_size;
                self.total_in_use_bytes -= chunk_size;

                // link list
                chunk.next = self.first_free_chunk;
                self.first_free_chunk = chunk;
            }
        }

        /// Return a bunch of chunks to the free list.
        pub fn freeChunks(self: *@This(), free_head: *ChunkHeader, free_tail: *ChunkHeader, num_chunks: usize) void {
            const byte_swing = @as(usize, num_chunks) * chunk_size;

            const locked = self.lock.acquire();
            defer locked.release();

            free_tail.next = self.first_free_chunk;
            self.first_free_chunk = free_head;

            self.total_free_list_bytes += byte_swing;
            self.total_in_use_bytes -= byte_swing;
        }
    };
}

test "Lazy Allocator" {
    const chunk_size: usize = 16 * 1024;

    var allocator = ThreadsafeChunkAllocator(chunk_size).init();
    testing.expect(isChunkAllocator(@TypeOf(allocator)));
    testing.expectEqual(@as(usize, 0), allocator.total_free_list_bytes);
    testing.expectEqual(@as(usize, 0), allocator.total_in_use_bytes);

    const chunk1 = try allocator.allocChunk();
    testing.expectEqual(allocator.allocation_granularity_bytes - chunk_size, allocator.total_free_list_bytes);
    testing.expectEqual(chunk_size, allocator.total_in_use_bytes);

    allocator.freeChunk(chunk1);
    testing.expectEqual(allocator.allocation_granularity_bytes, allocator.total_free_list_bytes);
    testing.expectEqual(@as(usize, 0), allocator.total_in_use_bytes);

    const chunk2 = try allocator.allocChunk();
    testing.expectEqual(allocator.allocation_granularity_bytes - chunk_size, allocator.total_free_list_bytes);
    testing.expectEqual(chunk_size, allocator.total_in_use_bytes);
    testing.expectEqual(chunk1, chunk2);

    while (allocator.first_free_chunk != null) {
        _ = try allocator.allocChunk();
    }

    testing.expectEqual(@as(usize, 0), allocator.total_free_list_bytes);
    testing.expectEqual(allocator.allocation_granularity_bytes, allocator.total_in_use_bytes);
}

test "Seed Allocator" {
    var allocator = ThreadsafeChunkAllocator(16 * 1024).init();
    testing.expectEqual(@as(usize, 0), allocator.total_free_list_bytes);
    testing.expectEqual(@as(usize, 0), allocator.total_in_use_bytes);
    testing.expect(allocator.first_free_chunk == null);

    try allocator.seed(16 * 1024 * 4);
    testing.expectEqual(@as(usize, 16 * 1024 * 4), allocator.total_free_list_bytes);
    testing.expectEqual(@as(usize, 16 * 1024 * 0), allocator.total_in_use_bytes);
    testing.expect(allocator.first_free_chunk != null);

    const chunk1 = try allocator.allocChunk();
    testing.expectEqual(@as(usize, 16 * 1024 * 3), allocator.total_free_list_bytes);
    testing.expectEqual(@as(usize, 16 * 1024 * 1), allocator.total_in_use_bytes);
    testing.expect(allocator.first_free_chunk != null);

    const chunk2 = try allocator.allocChunk();
    testing.expectEqual(@as(usize, 16 * 1024 * 2), allocator.total_free_list_bytes);
    testing.expectEqual(@as(usize, 16 * 1024 * 2), allocator.total_in_use_bytes);
    testing.expect(allocator.first_free_chunk != null);

    allocator.freeChunk(chunk2);
    testing.expectEqual(@as(usize, 16 * 1024 * 3), allocator.total_free_list_bytes);
    testing.expectEqual(@as(usize, 16 * 1024 * 1), allocator.total_in_use_bytes);
    testing.expect(allocator.first_free_chunk != null);

    const chunk3 = try allocator.allocChunk();
    testing.expectEqual(@as(usize, 16 * 1024 * 2), allocator.total_free_list_bytes);
    testing.expectEqual(@as(usize, 16 * 1024 * 2), allocator.total_in_use_bytes);
    testing.expectEqual(chunk2, chunk3);
    testing.expect(allocator.first_free_chunk != null);

    const chunk4 = try allocator.allocChunk();
    testing.expectEqual(@as(usize, 16 * 1024 * 1), allocator.total_free_list_bytes);
    testing.expectEqual(@as(usize, 16 * 1024 * 3), allocator.total_in_use_bytes);
    testing.expect(allocator.first_free_chunk != null);

    const chunk5 = try allocator.allocChunk();
    testing.expectEqual(@as(usize, 16 * 1024 * 0), allocator.total_free_list_bytes);
    testing.expectEqual(@as(usize, 16 * 1024 * 4), allocator.total_in_use_bytes);
    assert(allocator.first_free_chunk == null);
}
