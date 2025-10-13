/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define ALIGN_MASK (ALIGNMENT - 1)
#define ALLOC_MASK 0x1
#define PREV_ALLOC_MASK 0x2
#define WSIZE (ALIGN(sizeof(size_t))) 
#define DSIZE (2 * WSIZE)
#define MIN_BLOCK_SIZE (4 * WSIZE) 
#define NBINS 16

// Accessor for the i-th bin head stored in the heap area:
#define BIN_HEAD(i) (*((char**)(bin_table + (i) * WSIZE)))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + ALIGN_MASK) & ~ALIGN_MASK)

/* Pack a size and allocated bit into a word */
#define PACK(sz,a) (sz | (a ? ALLOC_MASK : 0))
#define PACKH(sz,a,pa) (sz | (a ? ALLOC_MASK : 0) | (pa ? PREV_ALLOC_MASK : 0))


/* Read and write a word at address p */
#define GET(p) (*(size_t*)(p))
#define PUT(p,val) (*(size_t*)(p) = (size_t)(val))

/* Read size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~(ALIGNMENT - 1))
#define GET_ALLOC(p) (GET(p) & ALLOC_MASK)
#define GET_PREV_ALLOC(p) (GET(p) & PREV_ALLOC_MASK)

#define HDR_SET_PREV_ALLOC(hp)  PUT(hp, GET(hp) | PREV_ALLOC_MASK)
#define HDR_CLR_PREV_ALLOC(hp)  PUT(hp, GET(hp) & ~PREV_ALLOC_MASK)

/* Given pointer p to payload, compute addr of headr and footer */
#define HDRP(p) ((char*)(p) - WSIZE)
#define FTRP(p) ((char*)(p) + GET_SIZE(HDRP(p)) - DSIZE)

/* Given pointer p to payload, compute addr of next and previous blocks */
#define PREV_BLKP(p) ((char*)(p) - GET_SIZE(((char*)(p) - DSIZE)))
#define NEXT_BLKP(p) ((char*)(p) + GET_SIZE(((char*)(p) - WSIZE)))

/* Given pointer p to free block, get next and previous ptrs */
#define PREV_PTR(p) ((char**)(p))
#define NEXT_PTR(p) ((char**)((char*)(p) + WSIZE))

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

/* Global variables */
static char* bin_table; /* Pointer to the start of the bin table */

/* Forward declarations */
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void insert_free_block(void* bp);
static void remove_free_block(void* bp);
static void* find_fit(size_t asize);
static void* extend_next(void* bp, size_t asize, size_t bsize);

/* extend_heap - extend heap by "amount" words, return pointer to new free block's payload */
static void* extend_heap(size_t amount)
{
    /* Allocate an even number of words to maintain alignment */
    size_t size = WSIZE * amount + ((amount % 2) ? WSIZE : 0);
    char* bp = mem_sbrk(size);
    if (bp == (char*)-1) return NULL;

    size_t pa = GET_PREV_ALLOC(HDRP(bp));

    PUT(HDRP(bp), PACKH(size, 0, pa));
    PUT(FTRP(bp), PACK(size, 0));

    PUT(HDRP(NEXT_BLKP(bp)), PACKH(0, 1, 0)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    bp = coalesce(bp);
    insert_free_block(bp);
    return bp;
}

static void* coalesce(void* bp)
{
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    /* Right Block free */
    if (!next_alloc) {
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    }

    /* Left Block free */
    if (!prev_alloc) {
        void* prev = PREV_BLKP(bp);
        remove_free_block(prev);
        size += GET_SIZE(HDRP(prev));
        bp = prev;
    }

    size_t pa = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACKH(size, 0, pa));
    PUT(FTRP(bp), PACK(size, 0));

    HDR_CLR_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));
    return bp;
}

static void insert_free_block(void* bp)
{
    if (!bp) return;
    size_t size = GET_SIZE(HDRP(bp));
    size_t index = bin_index(size);
    char* prev = NULL;
    char* head = BIN_HEAD(index);

    while (head && GET_SIZE(HDRP(head)) < size) {
        prev = head;
        head = *NEXT_PTR(head);
    }

    *PREV_PTR(bp) = prev;
    *NEXT_PTR(bp) = head;
    if (prev) *NEXT_PTR(prev) = bp;
    else BIN_HEAD(index) = bp;
    if (head) *PREV_PTR(head) = bp;
}

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

static void* find_fit(size_t asize)
{
    for (size_t i = bin_index(asize); i < NBINS; i++) {
        for (char* p = BIN_HEAD(i); p; p = *NEXT_PTR(p)) {
            if (GET_SIZE(HDRP(p)) >= asize) return p;
        }
    }
    return NULL;
}

static void* extend_next(void* ptr, size_t asize, size_t bsize) {
    char* next = NEXT_BLKP(ptr);
    if (!GET_ALLOC(HDRP(next))) {
        size_t combined = bsize + GET_SIZE(HDRP(next));
        if (combined >= asize) {
            remove_free_block(next);
            size_t diff = combined - asize;
            if (diff >= MIN_BLOCK_SIZE) {
                set_allocated(ptr, asize);

                char* rem = NEXT_BLKP(ptr);
                set_free(rem, diff);
                insert_free_block(rem);
            } else set_allocated(ptr, combined);
            return ptr;
        }
    }
    return NULL;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    mem_init();
    size_t pad = ALIGN((size_t)mem_heap_lo()) - (size_t)mem_heap_lo();
    size_t table_bytes = NBINS * WSIZE;
    size_t prologue_size = DSIZE + table_bytes;

    char* start = mem_sbrk(pad + 3 * WSIZE + table_bytes);
    if (start == (char*)-1) return -1; 
    start += pad;

    PUT(start, PACKH(prologue_size, 1, 1)); /* prologue header */ 

    /* Initialize bin table */
    bin_table = start + WSIZE;
    for (size_t i = 0; i < NBINS; i++) BIN_HEAD(i) = NULL;

    PUT(start + prologue_size - WSIZE, PACK(prologue_size, 1)); /* prologue footer */ 


    PUT(start + prologue_size, PACKH(0, 1, 1)); /* epilogue header */

    if (!extend_heap((1 << 6) / WSIZE)) return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
    void* mm_malloc(size_t size)
    {
        if (size == 0) return NULL;
        size_t asize = ALIGN(size) + WSIZE;
        if (asize < MIN_BLOCK_SIZE) asize = MIN_BLOCK_SIZE;

        char* bp = find_fit(asize);
        if (!bp) {
            bp = extend_heap(asize / WSIZE);
            if (!bp) return NULL;
        }

        remove_free_block(bp);
        size_t bsize = GET_SIZE(HDRP(bp));
        size_t diff = bsize - asize;
        if (diff >= MIN_BLOCK_SIZE) {
            set_allocated(bp, asize);

            char* rem = NEXT_BLKP(bp);
            set_free(rem, diff);
            insert_free_block(NEXT_BLKP(bp));
        } else set_allocated(bp, bsize);

        return bp;
    }

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (!ptr) return;
    set_free(ptr, GET_SIZE(HDRP(ptr)));
    insert_free_block(coalesce(ptr));
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void* mm_realloc(void *ptr, size_t size)
{
    if (!ptr) return mm_malloc(size);
    if (size == 0) { mm_free(ptr); return NULL; }

    size_t asize = ALIGN(size) + WSIZE;
    if (asize < MIN_BLOCK_SIZE) asize = MIN_BLOCK_SIZE;
    size_t bsize = GET_SIZE(HDRP(ptr));

    if (bsize >= asize) {
        size_t diff = bsize - asize;
        if (diff >= MIN_BLOCK_SIZE) {
            set_allocated(ptr, asize);

            char* rem = NEXT_BLKP(ptr);
            set_free(rem, diff);

            insert_free_block(coalesce(rem));
        }
        return ptr;
    }

    size_t need = asize - bsize;

    char* extend = extend_next(ptr, asize, bsize);
    if (extend) return extend;

    if (GET_SIZE(HDRP(NEXT_BLKP(ptr))) == 0) {
        if (!extend_heap(need / WSIZE)) return NULL;
        extend = extend_next(ptr, asize, bsize);
        if (extend) return extend;
    }

    if (!GET_PREV_ALLOC(HDRP(ptr))) {
        char* prev = PREV_BLKP(ptr);
        size_t combined = bsize + GET_SIZE(HDRP(prev));
        if (combined >= asize) {
            remove_free_block(prev);
            memmove(prev, ptr, bsize - WSIZE);

            size_t diff = combined - asize;
            if (diff >= MIN_BLOCK_SIZE) {
                set_allocated(prev, asize);

                char* rem = NEXT_BLKP(prev);
                set_free(rem, diff);
                insert_free_block(coalesce(rem));
            } else set_allocated(prev, combined);
            return prev;
        }

    }

    void* new_ptr = mm_malloc(size);
    if (!new_ptr) return NULL;
    size_t payload = bsize - WSIZE;
    payload = (payload < size) ? payload : size;
    memcpy(new_ptr, ptr, payload);
    mm_free(ptr);
    return new_ptr;
}

