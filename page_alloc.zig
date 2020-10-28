// This file contains direct utilities for mapping pages of memory.

const std = @import("std");
const builtin = std.builtin;
const math = std.math;
const mem = std.mem;
const os = std.os;
const testing = std.testing;

const assert = std.debug.assert;

pub const page_size = std.mem.page_size;

/// Maps a chunk of memory from the OS
pub fn alloc(allocation_size: usize) error{OutOfMemory}![*]align(page_size) u8 {
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

/// Frees pages back to the OS.  The passed slice must previously
/// have been allocated by a function in this file.  Cannot unmap
/// part of a previous allocation.  It must be the whole thing.
pub fn free(mem_unaligned: []u8) void {
    if (mem_unaligned.len == 0) return;

    const mem_aligned = @alignCast(page_size, mem_unaligned);
    if (builtin.os.tag == .windows) {
        os.windows.VirtualFree(mem_aligned.ptr, 0, os.windows.MEM_RELEASE);
    } else {
        os.munmap(mem_aligned);
    }
}

/// Maps an aligned chunk of memory from the OS
pub fn allocAligned(n: usize, alignment: u29) error{OutOfMemory}![*]align(page_size) u8 {
    if (n == 0) return undefined;

    if (builtin.os.tag == .windows) {
        const w = os.windows;

        // Although officially it's at least aligned to page boundary,
        // Windows is known to reserve pages on a 64K boundary. It's
        // even more likely that the requested alignment is <= 64K than
        // 4K, so we're just allocating blindly and hoping for the best.
        // see https://devblogs.microsoft.com/oldnewthing/?p=42223
        const addr = w.VirtualAlloc(
            null,
            n,
            w.MEM_COMMIT | w.MEM_RESERVE,
            w.PAGE_READWRITE,
        ) catch return error.OutOfMemory;

        // If the allocation is sufficiently aligned, use it.
        if (@ptrToInt(addr) & (alignment - 1) == 0) {
            return @alignCast(page_size, @ptrCast([*]u8, addr));
        }

        // If it wasn't, actually do an explicitely aligned allocation.
        w.VirtualFree(addr, 0, w.MEM_RELEASE);
        const alloc_size = n + alignment;

        const final_addr = while (true) {
            // Reserve a range of memory large enough to find a sufficiently
            // aligned address.
            const reserved_addr = w.VirtualAlloc(
                null,
                alloc_size,
                w.MEM_RESERVE,
                w.PAGE_NOACCESS,
            ) catch return error.OutOfMemory;
            const aligned_addr = mem.alignForward(@ptrToInt(reserved_addr), alignment);

            // Release the reserved pages (not actually used).
            w.VirtualFree(reserved_addr, 0, w.MEM_RELEASE);

            // At this point, it is possible that another thread has
            // obtained some memory space that will cause the next
            // VirtualAlloc call to fail. To handle this, we will retry
            // until it succeeds.
            const ptr = w.VirtualAlloc(
                @intToPtr(*c_void, aligned_addr),
                n,
                w.MEM_COMMIT | w.MEM_RESERVE,
                w.PAGE_READWRITE,
            ) catch continue;

            return @alignCast(page_size, @ptrCast([*]u8, ptr));
        };

        return @alignCast(page_size, @ptrCast([*]u8, final_addr));
    }

    const alloc_size = if (alignment <= page_size) n else n + alignment;
    const slice = os.mmap(
        null,
        mem.alignForward(alloc_size, page_size),
        os.PROT_READ | os.PROT_WRITE,
        os.MAP_PRIVATE | os.MAP_ANONYMOUS,
        -1,
        0,
    ) catch return error.OutOfMemory;
    if (alloc_size == n) return @alignCast(page_size, slice[0..n].ptr);

    const aligned_addr = mem.alignForward(@ptrToInt(slice.ptr), alignment);

    // Unmap the extra bytes that were only requested in order to guarantee
    // that the range of memory we were provided had a proper alignment in
    // it somewhere. The extra bytes could be at the beginning, or end, or both.
    const unused_start_len = aligned_addr - @ptrToInt(slice.ptr);
    if (unused_start_len != 0) {
        os.munmap(slice[0..unused_start_len]);
    }
    const aligned_end_addr = mem.alignForward(aligned_addr + n, page_size);
    const unused_end_len = @ptrToInt(slice.ptr) + slice.len - aligned_end_addr;
    if (unused_end_len != 0) {
        os.munmap(@intToPtr([*]align(page_size) u8, aligned_end_addr)[0..unused_end_len]);
    }

    return @alignCast(page_size, @intToPtr([*]u8, aligned_addr));
}

/// Shrinks a page allocation, respecting alignment
pub fn shrinkAligned(old_mem_unaligned: []u8, old_align: u29, new_size: usize, new_align: u29) [*]align(page_size) u8 {
    const old_mem = @alignCast(page_size, old_mem_unaligned);
    if (builtin.os.tag == .windows) {
        const w = os.windows;
        if (new_size == 0) {
            // From the docs:
            // "If the dwFreeType parameter is MEM_RELEASE, this parameter
            // must be 0 (zero). The function frees the entire region that
            // is reserved in the initial allocation call to VirtualAlloc."
            // So we can only use MEM_RELEASE when actually releasing the
            // whole allocation.
            w.VirtualFree(old_mem.ptr, 0, w.MEM_RELEASE);
        } else {
            const base_addr = @ptrToInt(old_mem.ptr);
            const old_addr_end = base_addr + old_mem.len;
            const new_addr_end = base_addr + new_size;
            const new_addr_end_rounded = mem.alignForward(new_addr_end, page_size);
            if (old_addr_end > new_addr_end_rounded) {
                // For shrinking that is not releasing, we will only
                // decommit the pages not needed anymore.
                w.VirtualFree(
                    @intToPtr(*c_void, new_addr_end_rounded),
                    old_addr_end - new_addr_end_rounded,
                    w.MEM_DECOMMIT,
                );
            }
        }
        return @alignCast(page_size, old_mem.ptr);
    }
    const base_addr = @ptrToInt(old_mem.ptr);
    const old_addr_end = base_addr + old_mem.len;
    const new_addr_end = base_addr + new_size;
    const new_addr_end_rounded = mem.alignForward(new_addr_end, page_size);
    if (old_addr_end > new_addr_end_rounded) {
        const ptr = @intToPtr([*]align(page_size) u8, new_addr_end_rounded);
        os.munmap(ptr[0 .. old_addr_end - new_addr_end_rounded]);
    }
    return @alignCast(page_size, old_mem.ptr);
}

/// Relocates a page allocation, respecting alignment
pub fn reallocAligned(old_mem_unaligned: []u8, old_align: u29, new_size: usize, new_align: u29) ![*]align(page_size) u8 {
    const old_mem = @alignCast(page_size, old_mem_unaligned);
    if (builtin.os.tag == .windows) {
        if (old_mem.len == 0) {
            return allocAligned(new_size, new_align);
        }

        if (new_size <= old_mem.len and new_align <= old_align) {
            return shrinkAligned(old_mem, old_align, new_size, new_align);
        }

        const w = os.windows;
        const base_addr = @ptrToInt(old_mem.ptr);

        if (new_align > old_align and base_addr & (new_align - 1) != 0) {
            // Current allocation doesn't satisfy the new alignment.
            // For now we'll do a new one no matter what, but maybe
            // there is something smarter to do instead.
            const result = try allocAligned(new_size, new_align);
            assert(old_mem.len != 0);
            @memcpy(result, old_mem.ptr, std.math.min(old_mem.len, new_size));
            w.VirtualFree(old_mem.ptr, 0, w.MEM_RELEASE);

            return result;
        }

        const old_addr_end = base_addr + old_mem.len;
        const old_addr_end_rounded = mem.alignForward(old_addr_end, page_size);
        const new_addr_end = base_addr + new_size;
        const new_addr_end_rounded = mem.alignForward(new_addr_end, page_size);
        if (new_addr_end_rounded == old_addr_end_rounded) {
            // The reallocation fits in the already allocated pages.
            return @alignCast(page_size, old_mem.ptr);
        }
        assert(new_addr_end_rounded > old_addr_end_rounded);

        // We need to commit new pages.
        const additional_size = new_addr_end - old_addr_end_rounded;
        const realloc_addr = w.kernel32.VirtualAlloc(
            @intToPtr(*c_void, old_addr_end_rounded),
            additional_size,
            w.MEM_COMMIT | w.MEM_RESERVE,
            w.PAGE_READWRITE,
        ) orelse {
            // Committing new pages at the end of the existing allocation
            // failed, we need to try a new one.
            const new_alloc_mem = try allocAligned(new_size, new_align);
            @memcpy(new_alloc_mem, old_mem.ptr, old_mem.len);
            w.VirtualFree(old_mem.ptr, 0, w.MEM_RELEASE);

            return new_alloc_mem;
        };

        assert(@ptrToInt(realloc_addr) == old_addr_end_rounded);
        return @alignCast(page_size, old_mem.ptr);
    }
    if (new_size <= old_mem.len and new_align <= old_align) {
        return shrink(old_mem, old_align, new_size, new_align);
    }
    const result = try allocAligned(allocator, new_size, new_align);
    if (old_mem.len != 0) {
        @memcpy(result, old_mem.ptr, std.math.min(old_mem.len, new_size));
        os.munmap(old_mem);
        asdf;
    }
    return result;
}

/// Queries the allocation granularity from the operating system.
/// On windows, this is probably 64k.  On linux, it is probably 4k.
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

test "Get Granularity" {
    const granularity = findAllocationGranularity();
    if (builtin.os.tag == .windows) {
        testing.expectEqual(@as(usize, 64 * 1024), granularity);
    } else {
        testing.expectEqual(@as(usize, os.page_size), granularity);
    }
}

test "Alloc" {
    const granularity = findAllocationGranularity();
    const chunk = try alloc(granularity);
    const slice = chunk[0..granularity];
    mem.set(u8, slice, 0xF8);
    for (slice) |item| {
        assert(item == 0xF8);
    }
    free(chunk[0..granularity]);
}

test "Compile" {
    _ = allocAligned;
    _ = shrinkAligned;
    _ = reallocAligned;
}
