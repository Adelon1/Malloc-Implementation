/*
 * mm.c - Segregated, sorted free list dynamic memory allocator
 * 
 * The allocator uses multiple segregated free lists, each storing free blocks
 * of different size classes. Each free list is sorted by block size to improve
 * allocation performance. Blocks are coalesced immediately upon freeing.
 * The allocator uses prologue and epilogue blocks to simplify boundary
 * conditions. Each block has a header (and footer if free) storing size and
 * allocation status. The previous block's allocation status is also stored in
 * the header.
 */

// Include necessary headers
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

// Constants
#define ALIGNMENT 8
#define ALIGN_MASK (ALIGNMENT - 1)
#define ALLOC_MASK 0x1
#define PREV_ALLOC_MASK 0x2
#define WSIZE (ALIGN(sizeof(size_t))) 
#define DSIZE (2 * WSIZE)
#define MIN_BLOCK_SIZE (4 * WSIZE) 
#define NBINS 16

// Access the i-th bin head stored in the heap area
#define BIN_HEAD(i) (*((char**)(bin_table + (i) * WSIZE)))

// rounds up to the nearest multiple of ALIGNMENT
#define ALIGN(size) (((size) + ALIGN_MASK) & ~ALIGN_MASK)

// Pack a size and allocation bits into a word
#define PACK(bsize,a) ((bsize) | ((a) ? ALLOC_MASK : 0))
#define PACKH(bsize,a,pa) ((bsize) | ((a) ? ALLOC_MASK : 0) | ((pa) ? PREV_ALLOC_MASK : 0))

// Read and write a word at address p
#define GET(bp) (*(size_t*)(bp))
#define PUT(bp,val) (*(size_t*)(bp) = (size_t)(val))

// Read size and allocation bits from address p
#define GET_SIZE(bp) (GET(bp) & ~(ALIGNMENT - 1))
#define GET_ALLOC(bp) (GET(bp) & ALLOC_MASK)
#define GET_PREV_ALLOC(bp) (GET(bp) & PREV_ALLOC_MASK)

// Set and clear the previous block's allocation bit
#define HDR_SET_PREV_ALLOC(bp)  PUT(bp, GET(bp) | PREV_ALLOC_MASK)
#define HDR_CLR_PREV_ALLOC(bp)  PUT(bp, GET(bp) & ~PREV_ALLOC_MASK)

// compute addr of header and footer
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// compute addr of next and previous blocks
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)))

// pointer in free block, get next and previous ptrs
#define PREV_PTR(bp) ((char**)(bp))
#define NEXT_PTR(bp) ((char**)((char*)(bp) + WSIZE))

// bin selector and block state updates
static inline size_t bin_index(size_t size) {
    size_t index = 0;
    size_t s = MIN_BLOCK_SIZE;
    while (size > s && index < NBINS - 1) {
        s <<= 1;
        index++;
    }
    return index;
}
static inline void set_allocated(void* bp, size_t asize) {  
    size_t pa = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACKH(asize, 1, pa));
    HDR_SET_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));
}
static inline void set_free(void* bp, size_t asize) {
    size_t pa = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACKH(asize, 0, pa));
    PUT(FTRP(bp), PACK(asize, 0));
    HDR_CLR_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));
}

// Pointer to the start of the segregated free list table
static char* bin_table;

// Forward declarations
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void  insert_free_block(void* bp);
static void  remove_free_block(void* bp);
static void* find_fit(size_t asize);
static void* extend_next(void* bp, size_t asize, size_t bsize);


// extend heap by 'words' words, return pointer to new free block's
static void* extend_heap(size_t words)
{
    // Ensure minimum block size and alignment
    size_t asize = (words < 4) ? MIN_BLOCK_SIZE : words * WSIZE;

    char* bp = mem_sbrk(asize);
    if (bp == (char*)-1) return NULL;

    // Initialize new free block and epilogue header
    size_t pa = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACKH(asize, 0, pa));
    PUT(FTRP(bp), PACK(asize, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACKH(0, 1, 0));

    bp = coalesce(bp);
    insert_free_block(bp);
    return bp;
}

// Coalesce adjacent free blocks and return pointer to the merged block
static void* coalesce(void* bp)
{
    size_t pa = GET_PREV_ALLOC(HDRP(bp));
    size_t na = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t bsize = GET_SIZE(HDRP(bp));
    
    // Merge with next block if free
    if (!na) {
        remove_free_block(NEXT_BLKP(bp));
        bsize += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    }

    // Merge with previous block if free
    if (!pa) {
        void* prev = PREV_BLKP(bp);
        remove_free_block(prev);
        bsize += GET_SIZE(HDRP(prev));
        bp = prev;
    }

    // Update header/footer and clear next block’s prev_alloc
    pa = GET_PREV_ALLOC(HDRP(bp)); 
    PUT(HDRP(bp), PACKH(bsize, 0, pa));
    PUT(FTRP(bp), PACK(bsize, 0));
    HDR_CLR_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));

    return bp;
}

// Insert a free block into its appropriate size bin in sorted order
static void insert_free_block(void* bp)
{
    if (!bp) return;
    size_t bsize = GET_SIZE(HDRP(bp));
    size_t index = bin_index(bsize);
    char* prev = NULL;
    char* head = BIN_HEAD(index);

    // Find the correct position to insert
    while (head && GET_SIZE(HDRP(head)) < bsize) {
        prev = head;
        head = *NEXT_PTR(head);
    }

    // Insert block between prev and head
    *PREV_PTR(bp) = prev;
    *NEXT_PTR(bp) = head;
    if (prev) *NEXT_PTR(prev) = bp;
    else BIN_HEAD(index) = bp;
    if (head) *PREV_PTR(head) = bp;
}

// Remove a free block from its bin’s linked list
static void remove_free_block(void* bp)
{
    if (!bp) return;
    char* prev = *PREV_PTR(bp);
    char* next = *NEXT_PTR(bp);

    if (prev) *NEXT_PTR(prev) = next;
    else BIN_HEAD(bin_index(GET_SIZE(HDRP(bp)))) = next;
    if (next) *PREV_PTR(next) = prev;

    *PREV_PTR(bp) = *NEXT_PTR(bp) = NULL;
}

// Find a free block of at least asize bytes using segregated bins
static void* find_fit(size_t asize)
{
    for (size_t i = bin_index(asize); i < NBINS; i++) {
        for (char* bp = BIN_HEAD(i); bp; bp = *NEXT_PTR(bp)) {
            if (GET_SIZE(HDRP(bp)) >= asize) return bp;
        }
    }
    return NULL;
}

// Try to extend the current block into the next free block if space allows
static void* extend_next(void* bp, size_t asize, size_t bsize) {
    char* next = NEXT_BLKP(bp);
    if (!GET_ALLOC(HDRP(next))) {
        size_t combined = bsize + GET_SIZE(HDRP(next));
        if (combined >= asize) {
            remove_free_block(next);
            size_t diff = combined - asize;
            if (diff >= MIN_BLOCK_SIZE) {
                set_allocated(bp, asize);

                char* rem = NEXT_BLKP(bp);
                set_free(rem, diff);
                insert_free_block(rem);
            } else set_allocated(bp, combined);
            return bp;
        }
    }
    return NULL;
}


// Initialize the memory allocator and set up the initial heap
int mm_init(void)
{
    mem_init();

    size_t pad = ALIGN((size_t)mem_heap_lo()) - (size_t)mem_heap_lo();
    size_t table_bytes = NBINS * WSIZE;
    size_t prologue_size = DSIZE + table_bytes;

    // Allocate space for padding, prologue, bin table, and epilogue
    char* start = mem_sbrk(pad + 3 * WSIZE + table_bytes);
    if (start == (char*)-1) return -1; 
    start += pad;

    // Prologue: header, payload = bin_table and footer
    PUT(start, PACKH(prologue_size, 1, 1)); /* prologue header */ 
    bin_table = start + WSIZE;
    for (size_t i = 0; i < NBINS; i++) BIN_HEAD(i) = NULL;
    PUT(start + prologue_size - WSIZE, PACK(prologue_size, 1)); /* prologue footer */ 

    // Epilogue: header
    PUT(start + prologue_size, PACKH(0, 1, 1)); /* epilogue header */

    return 0;
}

// Allocate a block of at least 'size' bytes, maintaining alignment
void* mm_malloc(size_t size)
{
    if (size == 0) return NULL;
    size_t asize = ALIGN(size) + WSIZE;
    if (asize < MIN_BLOCK_SIZE) asize = MIN_BLOCK_SIZE;

    // Find a fit or extend heap
    char* bp = find_fit(asize);
    if (!bp) {
        bp = extend_heap(asize / WSIZE);
        if (!bp) return NULL;
    }

    remove_free_block(bp);
    size_t bsize = GET_SIZE(HDRP(bp));
    size_t diff = bsize - asize;

    // Split block if remainder is large enough
    if (diff >= MIN_BLOCK_SIZE) {
        set_allocated(bp, asize);

        char* rem = NEXT_BLKP(bp);
        set_free(rem, diff);
        insert_free_block(rem);
    } else set_allocated(bp, bsize);

    return bp;
}

// Free a block and coalesce with adjacent free blocks
void mm_free(void *bp)
{
    if (!bp) return;
    set_free(bp, GET_SIZE(HDRP(bp)));
    insert_free_block(coalesce(bp));
}

// Reallocate a block to a new size, preserving existing data
void* mm_realloc(void *bp, size_t size)
{
    if (!bp) return mm_malloc(size);
    if (size == 0) { mm_free(bp); return NULL; }

    size_t asize = ALIGN(size) + WSIZE;
    if (asize < MIN_BLOCK_SIZE) asize = MIN_BLOCK_SIZE;
    size_t bsize = GET_SIZE(HDRP(bp));

    // Case 1: shrinking
    if (bsize >= asize) {
        size_t diff = bsize - asize;
        if (diff >= MIN_BLOCK_SIZE) {
            set_allocated(bp, asize);

            char* rem = NEXT_BLKP(bp);
            set_free(rem, diff);
            insert_free_block(coalesce(rem));
        }
        return bp;
    }

    // Case 2: try to expand to next block
    char* extend = extend_next(bp, asize, bsize);
    if (extend) return extend;

    // Case 3: try to extend heap if at the end
    size_t need = asize - bsize;
    if (GET_SIZE(HDRP(NEXT_BLKP(bp))) == 0) {
        if (!extend_heap(need / WSIZE)) return NULL;
        extend = extend_next(bp, asize, bsize);
        if (extend) return extend;
    }

    // Case 4: try to merge with previous block
    if (!GET_PREV_ALLOC(HDRP(bp))) {
        char* prev = PREV_BLKP(bp);
        size_t combined = bsize + GET_SIZE(HDRP(prev));

        // Case 4a: merge with previous only
        if (combined >= asize) {
            remove_free_block(prev);
            memmove(prev, bp, bsize - WSIZE);

            size_t diff = combined - asize;
            if (diff >= MIN_BLOCK_SIZE) {
                set_allocated(prev, asize);

                char* rem = NEXT_BLKP(prev);
                set_free(rem, diff);
                insert_free_block(coalesce(rem));
            } else set_allocated(prev, combined);
            return prev;
        }
        
        // Case 4b: merge with previous and next
        char* next = NEXT_BLKP(bp);
        size_t rcombined;
        if (!GET_ALLOC(HDRP(next)) && (rcombined = combined + GET_SIZE(HDRP(next))) >= asize) {
            remove_free_block(prev);
            memmove(prev, bp, bsize - WSIZE);

            set_allocated(prev, combined);
            return extend_next(prev, asize, combined);
        }
    }

    // Case 5: allocate new block and copy data
    void* new_bp = mm_malloc(size);
    if (!new_bp) return NULL;
    size_t payload = bsize - WSIZE;
    payload = (payload < size) ? payload : size;
    memcpy(new_bp, bp, payload);
    mm_free(bp);
    return new_bp;
}


// Check each block in the heap for consistency
int mm_checkheap()
{
    char* heap_lo = mem_heap_lo();
    char* heap_hi = mem_heap_hi() + 1;

    size_t pad = ALIGN((size_t)heap_lo) - (size_t)heap_lo;
    char*  base = heap_lo + pad;
    size_t table_bytes = NBINS * WSIZE;
    size_t prologue_size = DSIZE + table_bytes;

    // Check prologue block
    if (GET(base) != PACKH(prologue_size, 1, 1)) {
        printf("Bad prologue header\n");
        return 0;
    }
    if (GET(base + prologue_size - WSIZE) != PACK(prologue_size, 1)) {
        printf("Bad prologue footer\n");
        return 0;
    }

    char* bp = base + prologue_size + WSIZE;
    size_t pa = 1;
    size_t free_blocks = 0, free_bytes = 0;

    // Check each block in the heap
    while (bp < heap_hi) {
        size_t hsize = GET_SIZE(HDRP(bp));
        size_t ha = GET_ALLOC(HDRP(bp));
        size_t hpa = GET_PREV_ALLOC(HDRP(bp));

        // Check the epilogue block
        if (hsize == 0) {
            if (!ha) { printf("Epilogue header marked free\n"); return 0; }
            if (hpa != pa) { printf("Epilogue header has wrong prev alloc bit\n"); return 0; }
            break;
        }

        // Check size and alignment
        if ((hsize % WSIZE) != 0) { printf("Block size not aligned\n"); return 0; }
        if (hsize < MIN_BLOCK_SIZE) { printf("Block size too small\n"); return 0; }
        if ((size_t)bp & ALIGN_MASK) { printf("Block not aligned\n"); return 0; }

        // check previous block allocation status
        if (hpa != pa) { printf("Block has wrong prev alloc bit\n"); return 0; }

        // Check free block consistency
        if (!ha) {
            // check footer
            if (GET(FTRP(bp)) != PACK(hsize, 0)) { printf("Bad free block footer\n"); return 0; }

            // No two consecutive free blocks
            if (!pa) { printf("Two consecutive free blocks\n"); return 0; }

            free_blocks++;
            free_bytes += hsize;
        }

        // Move to next block
        pa = ha;
        bp += hsize;

        // Check if pointer is within heap bounds
        if (bp > heap_hi) { printf("Block extends beyond heap bounds\n"); return 0; }
    }
    
    // Check free list consistency
    size_t counted_free_blocks = 0, counted_free_bytes = 0;
    for (size_t i = 0; i < NBINS; i++) {
        char* head = BIN_HEAD(i);

        // prev pointer of head should be NULL
        if (head && *PREV_PTR(head) != NULL) { printf("Free list head has non-NULL prev pointer\n"); return 0; }

        // detect cycle 
        char* slow = head;
        char* fast = head;
        while (fast && *NEXT_PTR(fast)) {
            slow = *NEXT_PTR(slow);
            fast = *NEXT_PTR(*NEXT_PTR(fast));
            if (slow == fast) { printf("Cycle detected in free list\n"); return 0; }
        }

        // check each block in the free list
        size_t psize = 0;
        for (char* p = head; p; p = *NEXT_PTR(p)) {
            // aligned
            if ((size_t)p & ALIGN_MASK) { printf("Free block pointer not aligned\n"); return 0; }

            // marked free in header
            if (GET_ALLOC(HDRP(p))) { printf("Allocated block in free list\n"); return 0; }

            // size matches
            size_t s = GET_SIZE(HDRP(p));
            if (s < MIN_BLOCK_SIZE || (s % WSIZE) != 0) { printf("Free block with invalid size\n"); return 0; }

            // Header and footer match
            if (GET(FTRP(p)) != PACK(s, 0)) { printf("Free block header and footer do not match\n"); return 0; }

            // Bin index correct
            if (bin_index(s) != i) { printf("Free block in wrong bin\n"); return 0; }

            // sorted by size
            if (psize > s) { printf("Free list not sorted by size\n"); return 0; }
            psize = s;

            // prev and next pointers consistent
            char* next = *NEXT_PTR(p);
            if (next && *PREV_PTR(next) != p) { printf("Inconsistent prev pointer in free list\n"); return 0; }

            counted_free_blocks++;
            counted_free_bytes += s;
        }
    }

    // Check counts
    if (counted_free_blocks != free_blocks || counted_free_bytes != free_bytes) {
        printf("Free block counts do not match\n");
        return 0;
    }

    return 1;
}
