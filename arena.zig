const std = @import("std");
usingnamespace @import("chunk_alloc.zig");
const page_alloc = @import("page_alloc.zig");

const assert = std.debug.assert;
const mem = std.mem;
const math = std.math;
const Allocator = mem.Allocator;

const DirectAllocation = struct {
    next: ?*DirectAllocation,
    mem: []u8,
};

const ArenaMark = struct {
    current_offset: usize,
    num_chunks: usize,
    first_direct_alloc: ?*DirectAllocation,
    total_waste_bytes: usize,
    total_used_bytes: usize,
};

/// An allocator without free, where reset() frees all allocations.
/// Also supports mark() and restore() if you want to do a partial free.
pub fn Arena(comptime in_chunk_size: usize) type {
    return struct {
        pub const chunk_size = in_chunk_size;

        /// Chunks will be allocated from the parent
        parent: *ThreadsafeChunkAllocator(chunk_size),

        /// The head of the list of allocated chunks
        /// New allocations are always performed on the head page.
        /// The head page is never null, when pages are freed the
        /// front page is kept.
        list_head: *ChunkHeader,

        /// The tail of the list of allocated chunks
        /// Tracked to relocate the list into the allocator.
        list_tail: *ChunkHeader,

        /// The current offset in bytes on the list_head page.
        current_offset: usize,

        /// The number of chunks in the linked list.  Will always
        /// be at least 1.
        num_chunks: usize,

        /// The head of a linked list of large allocations, embedded
        /// in the normal list pages.  Large allocations are mapped
        /// directly, and one of these records is linked in.  When
        /// resetting the list, all of these are freed.
        first_direct_alloc: ?*DirectAllocation,

        /// The total number of bytes lost to padding or internal tracking.
        total_waste_bytes: usize,

        /// The total number of bytes allocated to callers.  Large allocations
        /// that are mapped directly do not count towards this value.
        total_used_bytes: usize,

        /// Creates an arena allocator.  Must allocate one page, which may error.
        pub fn init(parent: *ThreadsafeChunkAllocator(chunk_size)) !@This() {
            const init_chunk = try parent.allocChunk();
            const init_head = @ptrCast(*ChunkHeader, init_chunk);
            return @This(){
                .parent = parent,
                .list_head = init_head,
                .list_tail = init_head,
                .current_offset = @sizeOf(ChunkHeader),
                .num_chunks = 1,
                .first_direct_alloc = null,
                .total_waste_bytes = 0,
                .total_used_bytes = 0,
            };
        }

        /// Allocates a number of bytes, obtaining an extra page if necessary.
        /// Very large allocations will be mapped directly, but noted and freed
        /// on reset.
        pub fn allocBytes(self: *@This(), size: usize, alignment: u29) Error![*]u8 {
            const aligned_offset = mem.alignForward(self.current_offset, alignment);
            // fast path: allocation fits on page
            if (aligned_offset + size <= chunk_size) {
                // track stats
                self.total_used_bytes += size;
                self.total_waste_bytes += (aligned_offset - self.current_offset);
                // bump alloc
                self.current_offset = aligned_offset + size;
                return @ptrCast([*]u8, self.list_head) + aligned_offset;
            } else {
                // allocation doesn't fit on this page
                // check if this allocation fits in a chunk at all
                if (math.max(size, alignment) <= mem.page_size / 2) {
                    // gotta get a new chunk
                    const new_chunk = try self.parent.allocChunk();
                    const new_head = @ptrCast(*ChunkHeader, new_chunk);

                    // link it
                    new_head.next = self.list_head;
                    self.list_head = new_head;

                    // track stats and reset
                    self.total_waste_bytes += (chunk_size - self.current_offset);
                    self.current_offset = @sizeOf(ChunkHeader);

                    // alloc from new chunk
                    const new_aligned_offset = mem.alignForward(@sizeOf(ChunkHeader), alignment);
                    assert(new_aligned_offset + size < chunk_size);
                    // track stats
                    self.total_used_bytes += size;
                    self.total_waste_bytes += (new_aligned_offset - self.current_offset);

                    // offset the pointer
                    self.current_offset = new_aligned_offset + size;
                    return @ptrCast([*]u8, new_head) + aligned_offset;
                } else {
                    // allocation doesn't fit on any page
                    // this needs to be a direct allocation
                    const allocation = try page_alloc.allocAligned(size, alignment);
                    errdefer page_alloc.free(allocation[0..size]);

                    // store it in the linked list so we can free it on reset
                    const direct = try self.create(DirectAllocation);

                    // don't count the direct allocation as used
                    self.total_used_bytes -= @sizeOf(DirectAllocation);
                    self.total_waste_bytes += @sizeOf(DirectAllocation);

                    // link in the new node
                    direct.* = DirectAllocation{
                        .next = self.first_direct_alloc,
                        .mem = allocation[0..size],
                    };
                    self.first_direct_alloc = direct;
                    return allocation;
                }
            }
        }

        /// Reallocates bytes, changing their allocated size or alignment.
        /// May relocate the passed slice.  Returns a pointer to the new memory.
        pub fn reallocBytes(self: *@This(), bytes: []u8, alignment: u29, new_size: usize, new_alignment: u29) Error![*]u8 {
            const bytes_end = bytes.ptr + bytes.len;
            const page_end = @ptrCast([*]u8, self.list_head) + self.current_offset;

            // If it fits in the existing allocation, just return the same pointer.
            // We can free up some space if this is the last allocation.
            if (new_size == 0 or (new_size <= bytes.len and mem.isAligned(bytes.ptr, new_alignment))) {
                if (bytes_end == page_end) {
                    self.current_offset -= bytes.len - new_size;
                }
                return bytes.ptr;
            }

            // Otherwise we need to make a new allocation.
            // If this was the last thing we allocated, we can "free" it first.
            if (bytes_end == page_end) {
                self.current_offset -= bytes.len;
            }
            // If the new allocation fails, restore the original allocation.
            errdefer if (bytes_end == page_end) {
                self.current_offset += bytes.len;
            };

            // Allocate new memory
            const new_mem = try self.allocBytes(new_size, new_alignment);

            // If it's not the same pointer, we need to copy the data.
            // It may be the same pointer if the alignment is the same
            // and we just "freed" the original.
            if (new_mem != bytes.ptr) {
                const copy_size = math.min(bytes.len, new_size);
                // check if the slices overlap.
                // they can only overlap forwards, never backwards.
                if (new_mem - bytes.ptr < copy_size) {
                    var i = copy_size;
                    while (i > 0) {
                        i -= 1;
                        // "unsafe" slice access here to avoid bounds
                        // check on every access in safe modes
                        new_mem[i] = bytes.ptr[i];
                    }
                } else {
                    // no alias, use a fast memcpy
                    @memcpy(new_mem, bytes.ptr, copy_size);
                }
            }

            return new_mem;
        }

        /// Allocates a slice
        pub fn alloc(self: *@This(), comptime T: type, count: usize) ![]T {
            const ptr = try self.allocBytes(@sizeOf(T) * count, @alignOf(T));
            return @ptrCast([*]T, @alignCast(@alignOf(T), ptr))[0..count];
        }

        /// Allocates an aligned slice
        pub fn allocAligned(self: *@This(), comptime T: type, count: usize, comptime alignment: comptime_int) ![]align(alignment) T {
            const ptr = try self.allocBytes(@sizeOf(T) * count, alignment);
            return @ptrCast([*]align(alignment) T, @alignCast(alignment, ptr))[0..count];
        }

        /// Allocates a single instance
        pub fn create(self: *@This(), comptime T: type) !*T {
            const ptr = try self.allocBytes(@sizeOf(T), @alignOf(T));
            return @ptrCast(*T, @alignCast(@alignOf(T), ptr));
        }

        /// Allocates a single aligned instance
        pub fn createAligned(self: *@This(), comptime T: type, comptime alignment: comptime_int) !*align(alignment) T {
            const ptr = try self.allocBytes(@sizeOf(T), alignment);
            return @ptrCast(*align(alignment) T, @alignCast(alignment, ptr));
        }

        /// Duplicates a slice
        pub fn dupe(self: *@This(), comptime T: type, src: []const T) ![]T {
            const dest = try self.alloc(T, src.len);
            mem.copy(T, dest, src);
            return dest;
        }

        /// Creates a restore point.  `restore` can be called later to free everything
        /// allocated after this point.  The mark is invalidated if the arena is reset,
        /// or if a previous mark is restored.
        pub fn mark(self: @This()) ArenaMark {
            return ArenaMark{
                .current_offset = self.current_offset,
                .num_chunks = self.num_chunks,
                .first_direct_alloc = self.first_direct_alloc,
                .total_waste_bytes = self.total_waste_bytes,
                .total_used_bytes = self.total_used_bytes,
            };
        }

        /// Restores the arena to a mark point.
        pub fn restore(self: *@This(), the_mark: ArenaMark) void {
            // free direct allocations down to the target
            var direct_alloc = self.first_direct_alloc;
            while (direct_alloc != the_mark.first_direct_alloc) {
                const direct = direct_alloc.?;
                page_alloc.free(direct.mem);
                direct_alloc = direct.next;
            }

            // free any extra pages
            const pages_to_free = self.num_chunks - the_mark.num_chunks;
            if (pages_to_free > 0) {
                const first_page = self.list_head;
                var last_page = first_page;
                var pages_left = pages_to_free - 1;
                while (pages_left > 0) : (pages_left -= 1) {
                    last_page = last_page.next.?;
                }
                self.list_head = last_page.next.?;
                last_page.next = null;
                self.parent.freeChunks(first_page, last_page, pages_to_free);
            }

            // restore the state
            self.current_offset = the_mark.current_offset;
            self.num_chunks = the_mark.num_chunks;
            self.first_direct_alloc = the_mark.first_direct_alloc;
            self.total_waste_bytes = the_mark.total_waste_bytes;
            self.total_used_bytes = the_mark.total_used_bytes;
        }

        /// Resets the allocator, freeing all allocations.  Note that
        /// one chunk from the parent allocator is retained.  Call
        /// deinit() instead if you want to release everything.
        pub fn reset(self: *@This()) void {
            // free all direct allocations
            var direct_alloc = self.first_direct_alloc;
            while (direct_alloc) |direct| : (direct_alloc = direct.next) {
                page_alloc.free(direct.mem);
            }

            // return pages to shared pool, except head
            if (self.list_head.next != null) {
                self.parent.freeChunks(self.list_head.next.?, self.list_tail, self.num_chunks);
                self.list_head.next = null;
                self.list_tail = self.list_head;
            }

            // reset state
            self.current_offset = @sizeOf(ChunkHeader);
            self.num_chunks = 1;
            self.first_direct_alloc = null;
            self.total_waste_bytes = 0;
            self.total_used_bytes = 0;
        }

        /// Frees all allocations and releases all chunks back to the parent.
        /// Leaves this allocator in an undefined state.
        pub fn deinit(self: *@This()) void {
            // free all direct allocations
            var direct_alloc = self.first_direct_alloc;
            while (direct_alloc) |direct| : (direct_alloc = direct.next) {
                page_alloc.free(direct.mem);
            }

            // return pages to shared pool, including head
            self.parent.freeChunks(self.list_head, self.list_tail, self.num_chunks);

            self.* = undefined;
        }
    };
}

test "Arena" {
    const chunk_size = 16 * 1024;
    var root = ThreadsafeChunkAllocator(chunk_size).init();
    var arena = try Arena(chunk_size).init(&root);
    _ = try arena.alloc(u32, 10);
    _ = try arena.create(u32);
    const mark = arena.mark();
    _ = try arena.allocAligned(u32, 1, 1);
    _ = try arena.createAligned(u32, 1);
    _ = try arena.dupe(u8, "TheString");
    arena.restore(mark);
    arena.reset();
    arena.deinit();
}
