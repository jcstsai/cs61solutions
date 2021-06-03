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
#include <limits.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "jtsai",
    /* First member's full name */
    "John Tsai",
    /* First member's email address */
    "jtsai",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/*
 * If NEXT_FIT defined use next fit search, else use first fit search
 */
#define NEXT_FITx

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)           (*(unsigned int *)(p))
#define PUT(p, val)      (*(unsigned int *)(p) = (val))
#define PUT_ADDR(p, val) (*(void **)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define PRVP(bp)       ((void **)(bp))
#define NXTP(bp)       ((void **)(bp) + 1)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static void *freelistp = NULL; /* Pointer to first free block */
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void add_to_list(void *bp);
static void remove_from_list(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // Create the initial empty heap (4 words)
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) return -1;
    
    // Reset freelistp
    freelistp = NULL;
    
    // Add alignment padding (word 0), prologue (word 1), epilogue (word 3)
    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);
    
#ifdef NEXT_FIT
    rover = heap_listp;
#endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // Ignore spurious requests
    if (size == 0) return NULL;
    
    // If still at the start, initialize the heap
    if (heap_listp == 0) {
        mm_init();
    }
    
    // Adjust block size to include overhead and alignment reqs.
    size_t asize;
    if (size <= DSIZE) asize = 2*DSIZE;
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    // Search the free list for a fit
    char *bp;
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // No fit found. Get more memory and place the block
    size_t extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Free a block
 */
void mm_free(void *ptr)
{
    // don't free a null pointer
    if(ptr == 0) return;
    
    // if still at the start, initialize the heap
    if (heap_listp == 0) {
        mm_init();
    }

    // mark the block as freed and coalesce
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    add_to_list(ptr);
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * TODO clean up
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
    mm_free(ptr);
    return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
    return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
    return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize) {
#ifdef NEXT_FIT
    // Next fit search
    char *oldrover = rover;

    // Search from the rover to the end of list
    for (; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    // search from start of list to old rover
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
    if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
        return rover;

    // no fit
    return NULL;
#else
    // if no free blocks in the list, return null
    if (freelistp == NULL) {
        return NULL;
    }
    
    void *bp;
    unsigned int size;
    unsigned int minsize = UINT_MAX;
    void *minbp = NULL;

    for (bp = freelistp; bp != NULL; bp = *NXTP(bp)) {
        size = GET_SIZE(HDRP(bp));
        if (!GET_ALLOC(HDRP(bp)) && (asize <= size) && (size <= minsize)) {
            minbp = bp;
            minsize = size;
            
            if (asize == minsize) {
                break;
            }
        }
    }
    
    return minbp;
#endif
}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    add_to_list(bp);

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        // case 1: previous and next are both allocated
        return bp;
    } else if (prev_alloc && !next_alloc) {
        // case 2: previous is allocated, next is not
        remove_from_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    } else if (!prev_alloc && next_alloc) {
        // case 3: next is allocated, previous is not
        remove_from_list(bp);
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        // case 4: both prev and next are free
        remove_from_list(NEXT_BLKP(bp));
        remove_from_list(bp);
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

#ifdef NEXT_FIT
    // Make sure the rover isn't pointing into the free block
    // that we just coalesced. If so, point it to the start.
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp)))
        rover = bp;
#endif

    return bp;
}

/*
 * place - Place block of asize bytes at start of free block bp
 * and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        // split case
        // allocated block
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        remove_from_list(bp);
        
        // new free block
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        add_to_list(bp);
    } else {
        // don't split case
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        
        // remove block from free list
        remove_from_list(bp);
    }
}

/*
 * add_to_list - add the given block to the free list
 */
static void add_to_list(void *bp) {
    // set new block as prev block of first
    if (freelistp != NULL) PUT_ADDR(PRVP(freelistp), bp);

    // set next block of bp to old first block
    PUT_ADDR(NXTP(bp), freelistp);
    
    // set start of list to bp
    PUT_ADDR(PRVP(bp), NULL);
    freelistp = (void *)(bp);
}

/*
 * remove_from_list - remove the given block from the free list
 */
static void remove_from_list(void *bp) {
    // remove from prev
    if (*PRVP(bp) != NULL) PUT_ADDR(NXTP(*PRVP(bp)), *NXTP(bp));
    
    // remove from next
    if (*NXTP(bp) != NULL) PUT_ADDR(PRVP(*NXTP(bp)), *PRVP(bp));
    
    // set start of list if needed
    if (bp == freelistp) freelistp = *NXTP(bp);
}
