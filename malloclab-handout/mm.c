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
#define WSIZE (ALIGN(sizeof(size_t))) 
#define DSIZE (2 * WSIZE)
#define MIN_BLOCK_SIZE (4 * WSIZE) 


/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + ALIGN_MASK) & ~ALIGN_MASK)

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(size_t*)(p))
#define PUT(p,val) (*(size_t*)(p) = (size_t)(val))

/* Read size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~(ALIGNMENT - 1))
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given pointer p to payload, compute addr of headr and footer */
#define HDRP(p) ((char*)(p) - WSIZE)
#define FTRP(p) ((char*)(p) + GET_SIZE(HDRP(p)) - DSIZE)

/* Given pointer p to payload, compute addr of next and previous blocks */
#define PREV_BLKP(p) ((char*)(p) - GET_SIZE(((char*)(p) - DSIZE)))
#define NEXT_BLKP(p) ((char*)(p) + GET_SIZE(((char*)(p) - WSIZE)))

/* Given pointer p to free block, get next and previous ptrs */
#define PREV_PTR(p) ((char**)(p))
#define NEXT_PTR(p) ((char**)((char*)(p) + WSIZE))


/* Global variables */
static char* heap_listp;      /* points to prologue's payload */
static char* free_listp;      /* points to first free block */
const size_t CHUNKSIZE;


/* Forward declarations */
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void insert_free_block(void* bp);
static void remove_free_block(void* bp);
static void* find_fit(size_t asize);

/* extend_heap - extend heap by "amount" words, return pointer to new free block's payload */
static void* extend_heap(size_t amount)
{
    char* bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = WSIZE * amount + ((amount % 2) ? WSIZE : 0);
    if ((bp = mem_sbrk(size)) == (char*)-1) return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    insert_free_block(bp);
    return coalesce(bp);
}

static void* coalesce(void* bp)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* No free blocks around bp*/
    if (prev_alloc && next_alloc) return bp;    
    
    /* Right Block free */
    if (!next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_free_block(NEXT_BLKP(bp));
    }

    /* Left Block free */
    if (!prev_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_free_block(bp);
        bp = PREV_BLKP(bp);
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    return bp;
}

static void insert_free_block(void* bp)
{
    if (!bp) return;
    char* old_head = free_listp;
    char* prev = NULL;
    char* addr = (char*)bp;

    while (old_head && old_head < addr) {
        prev = old_head;
        old_head = *NEXT_PTR(old_head);
    }

    *PREV_PTR(addr) = prev;
    *NEXT_PTR(addr) = old_head;

    if (prev) *NEXT_PTR(prev) = addr;
    else free_listp = addr;
    if (old_head) *PREV_PTR(old_head) = addr;
}

static void remove_free_block(void* bp)
{
    if (!bp) return;
    char* prev = *PREV_PTR(bp);
    char* next = *NEXT_PTR(bp);

    if (prev) *NEXT_PTR(prev) = next;
    else free_listp = next;
    if (next) *PREV_PTR(next) = prev;

    *PREV_PTR(bp) = NULL;
    *NEXT_PTR(bp) = NULL;
}

static void* find_fit(size_t asize)
{
    char* curr = free_listp;
    while (curr) {
        if (GET_SIZE(HDRP(curr)) >= asize) return curr;
        curr = *NEXT_PTR(curr);
    }
    return NULL;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    mem_init();
    char* start = mem_sbrk(0);
    if (start == (char*)-1) return -1;

    size_t pad = ALIGN((size_t)start) - (size_t)start;
    start = mem_sbrk(pad + 3 * WSIZE);
    if (start == (char*)-1) return -1; 
    PUT(start + pad, PACK(DSIZE, 1)); /* prologue header */ 
    PUT(start + pad + WSIZE, PACK(DSIZE, 1)); /* prologue footer */ 
    PUT(start + pad + 2 * WSIZE, PACK(0, 1));     /* epilogue header */

    heap_listp = (char*)start + pad + WSIZE; 

    /* Extend the heap */
    free_listp = NULL;
    size_t pagesize = ALIGN(mem_pagesize());
    if (!extend_heap(pagesize / WSIZE)) return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void* mm_malloc(size_t size)
{
    if (size == 0) return NULL;
    size_t asize = (size <= WSIZE) ? MIN_BLOCK_SIZE : ALIGN(size) + DSIZE;

    char* bp = find_fit(asize);
    if (!bp) {
        asize = (asize > CHUNKSIZE) ? asize : CHUNKSIZE;
        bp = extend_heap(asize / WSIZE);
        if (!bp) return NULL;
    }

    size_t bsize = GET_SIZE(HDRP(bp));
    size_t diff = bsize - asize;
    if (diff < MIN_BLOCK_SIZE) {
        remove_free_block(bp);
        PUT(HDRP(bp), PACK(bsize, 1));
        PUT(FTRP(bp), PACK(bsize, 1));
    }
    else {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        char* next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(diff, 0));
        PUT(FTRP(next_bp), PACK(diff, 0));

        char* prev = *PREV_PTR(bp);
        char* next = *NEXT_PTR(bp);
        *PREV_PTR(next_bp) = prev;
        *NEXT_PTR(next_bp) = next;
        if (prev) *NEXT_PTR(prev) = next_bp;
        else free_listp = next_bp;
        if (next) *PREV_PTR(next) = next_bp;
    }

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - WSIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














