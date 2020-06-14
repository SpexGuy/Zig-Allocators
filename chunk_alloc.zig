// packages
const std = @import("std");

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

// constants
const page_size = mem.page_size;

/// An allocator that allocates large chunks from the operating system.
/// If the chunk size is smaller than the OS memory map granularity,
/// os allocations will be broken up into chunks and stored into a free list.
/// This allocator never decommits memory, it only grows.
pub fn ThreadsafeChunkAllocator(comptime in_chunk_size: usize) type {
    if (!math.isPowerOfTwo(in_chunk_size)) @compileError("Chunk size must be a power of two");
    if (in_chunk_size < page_size) @compileError("Chunk size must be greater than or equal to page size");
    return struct {
        pub const Error = error{OutOfMemory};

        /// The size of a chunk.  All chunks are exactly this size, with no waste.
        pub const chunk_size = in_chunk_size;

        /// A pointer to a data chunk of constant size
        pub const ChunkPtr = *align(page_size) [chunk_size]u8;

        /// Linked list data format for the free list of chunks.
        /// Chunks in the free list can be reinterpreted as this.
        const ChunkHeader = struct { next: ?ChunkPtr };

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
        first_free_chunk: ?ChunkPtr,

        /// Initialize a chunk allocator.  Queries the OS to get allocation granularity.
        /// This allocator is meant to be global and everlasting.  It cannot release
        /// virtual address space.  Once initialized, this allocator cannot be disposed.
        pub fn init() @This() {
            return @This(){
                .allocation_granularity_bytes = findAllocationGranularity(),
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

            var new_tail_chunk: ?ChunkPtr = null;
            var new_head_chunk: ?ChunkPtr = null;
            var remaining_bytes = actual_bytes;
            var allocation_size = actual_bytes;

            // Try to allocate the requested amount.  If an allocation fails,
            // try to make multiple smaller allocations.
            while (remaining_bytes > 0 and allocation_size >= granule_size) {
                if (mapChunksDirect(allocation_size)) |new_bytes| {
                    // link the chunks together in the new allocation
                    const head = @ptrCast(ChunkPtr, new_bytes);
                    var tail = head;
                    var offset = chunk_size;
                    while (offset < allocation_size) : (offset += chunk_size) {
                        const next_tail = @ptrCast(ChunkPtr, @alignCast(page_size, new_bytes + offset));
                        @ptrCast(*ChunkHeader, tail).next = next_tail;
                        tail = next_tail;
                    }

                    // link into the larger list
                    @ptrCast(*ChunkHeader, tail).next = new_tail_chunk;
                    if (new_tail_chunk == null) new_tail_chunk = tail;
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
                @ptrCast(*ChunkHeader, tail).next = self.first_free_chunk;
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
                    const header = @ptrCast(*ChunkHeader, chunk);
                    self.first_free_chunk = header.next;
                    return chunk;
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
                    const header = @ptrCast(*ChunkHeader, chunk);
                    self.first_free_chunk = header.next;
                    return chunk;
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

                const new_chunks = try mapChunksDirect(self.allocation_granularity_bytes);
                const first_chunk = @ptrCast(ChunkPtr, new_chunks);
                const second_chunk = @ptrCast(ChunkPtr, new_chunks + chunk_size);

                // link all chunks starting at the second chunk together.
                // we don't need the lock because these chunks aren't published.
                var last_chunk = second_chunk;
                var offset = chunk_size + chunk_size;
                while (offset < self.allocation_granularity_bytes) : (offset += chunk_size) {
                    const next_chunk = @ptrCast(ChunkPtr, @alignCast(page_size, new_chunks + offset));
                    @ptrCast(*ChunkHeader, last_chunk).next = next_chunk;
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
                    @ptrCast(*ChunkHeader, last_chunk).next = self.first_free_chunk;
                    self.first_free_chunk = second_chunk;
                }

                // return the first chunk
                return first_chunk;
            } else {
                const new_chunk = try mapChunksDirect(chunk_size);
                return @ptrCast(ChunkPtr, new_chunk);
            }
        }

        /// Returns a chunk to the free list.  This chunk remains committed and available.
        pub fn freeChunk(self: *@This(), chunk_ptr: [*]u8) void {
            const chunk = @ptrCast(ChunkPtr, @alignCast(page_size, chunk_ptr));
            {
                const locked = self.lock.acquire();
                defer locked.release();

                // update stats
                self.total_free_list_bytes += chunk_size;
                self.total_in_use_bytes -= chunk_size;

                // link list
                @ptrCast(*ChunkHeader, chunk).next = self.first_free_chunk;
                self.first_free_chunk = chunk;
            }
        }
    };
}

/// Queries the allocation granularity from the operating system
pub fn findAllocationGranularity() usize {
    if (builtin.os.tag == .windows) {
        const w = os.windows;
        var info: w.SYSTEM_INFO = undefined;
        w.kernel32.GetSystemInfo(&info);
        assert(math.isPowerOfTwo(info.dwAllocationGranularity));
        return info.dwAllocationGranularity;
    } else {
        return page_size;
    }
}

/// Maps a chunk of memory from the OS
pub fn mapChunksDirect(allocation_size: usize) error{OutOfMemory}![*]align(page_size) u8 {
    if (builtin.os.tag == .windows) {
        const w = os.windows;

        const addr = w.VirtualAlloc(
            null,
            allocation_size,
            w.MEM_COMMIT | w.MEM_RESERVE,
            w.PAGE_READWRITE,
        ) catch return error.OutOfMemory;

        return @alignCast(page_size, @ptrCast([*]u8, addr));
    } else {
        const slice = os.mmap(
            null,
            allocation_size,
            os.PROT_READ | os.PROT_WRITE,
            os.MAP_PRIVATE | os.MAP_ANONYMOUS,
            -1,
            0,
        ) catch return error.OutOfMemory;

        return slice.ptr;
    }
}

test "Get Granularity" {
    const granularity = findAllocationGranularity();
    if (builtin.os.tag == .windows) {
        testing.expectEqual(@as(usize, 64 * 1024), granularity);
    } else {
        testing.expectEqual(@as(usize, os.page_size), granularity);
    }
}

test "Map Chunk" {
    const granularity = findAllocationGranularity();
    const chunk = try mapChunksDirect(granularity);
    const slice = chunk[0..granularity];
    mem.set(u8, slice, 0xF8);
    for (slice) |item| {
        assert(item == 0xF8);
    }
}

test "Lazy Allocator" {
    const chunk_size: usize = 16 * 1024;

    var allocator = ThreadsafeChunkAllocator(chunk_size).init();
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
