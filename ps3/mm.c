/*
 * mm.c - a custom implementation of malloc.
 *
 * traces
 * 4 - 
 * 7 - allocate a bunch of 448/64, free the 448's, allocate a bunch more 512's
 * 8 - allocate a bunch of 112/16, free the 112's, allocate a bunch more 128's
 * 9 - should keep [128][512 +++++++>>>>.....
 * 10- should keep [16][4092 +++++++..>>>>>
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <limits.h>
#include <unistd.h>
#include <string.h>
#include <math.h>
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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<8)  /* Extend heap by this amount (bytes) */
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

/* number of free lists */
#define NUM_FREE_LISTS 128

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static void *freelistp[NUM_FREE_LISTS]; /* Pointer to first free blocks */

/* Function prototypes for internal helper routines */
static int mm_check();
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void add_to_list(void *bp);
static void remove_from_list(void *bp);
static int get_index(size_t size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // Create the initial empty heap (4 words)
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) return -1;
    
    // Reset freelistp
    for (int i = 0; i < NUM_FREE_LISTS; i++) freelistp[i] = NULL;
    
    // Add alignment padding (word 0), prologue (word 1), epilogue (word 3)
    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));
    heap_listp += (2*WSIZE);

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
    //printf("Allocating %d\n", size);

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
    
    //printf("Adjallocating %d\n", asize);

    // Search the free list for a fit
    char *bp;
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        
        // check heap consistency
        //if (mm_check()) exit(1);
        //printf("Allocated %p\n", bp);

        return bp;
    }

    // No fit found. Get more memory and place the block
    size_t extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
    place(bp, asize);
    
    // check heap consistency
    //if (mm_check()) exit(1);
    //printf("Allocated %p\n", bp);
    
    return bp;
}

/*
 * mm_free - Free a block
 */
void mm_free(void *ptr)
{   
    //printf("Free %p\n", ptr);
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
    
    // check heap consistency
    //printf("Freed %p\n", ptr);
    //if (mm_check()) exit(1);
}

/*
 * mm_realloc - reallocates a block

 */
void *mm_realloc(void *ptr, size_t size)
{
    //printf("Realloc %p %d\n", ptr, size);
    
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
    
    /* If the new size is less than the old size, use the same block */
    // Adjust block size to include overhead and alignment reqs.
    size_t asize;
    if (size <= DSIZE) asize = 2*DSIZE;
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    if ((asize == GET_SIZE(HDRP(ptr)) || asize < GET_SIZE(HDRP(ptr)) - 16) &&
        GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
        int csize = GET_SIZE(HDRP(ptr));
        
        // resize the allocated block
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        
        if (asize < csize) {
            void *bp = NEXT_BLKP(ptr);

            // resize the next free block
            PUT(HDRP(bp), PACK(csize-asize, 0));
            PUT(FTRP(bp), PACK(csize-asize, 0));
            add_to_list(bp);
            coalesce(bp);
        }
        newptr = ptr;
    } else if (
            ((asize == (GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))))) || 
               (asize + 16 < (GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr)))))
            ) &&
                !GET_ALLOC(HDRP(NEXT_BLKP(ptr))) &&
                GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
        // remove the next free block from the free list
        void *bp = NEXT_BLKP(ptr);
        int csize = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        remove_from_list(bp);  
                
        // resize the allocated block
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        
        bp = NEXT_BLKP(ptr);

        if (asize < csize) {
            // resize the next free block
            PUT(HDRP(bp), PACK(csize-asize, 0));
            PUT(FTRP(bp), PACK(csize-asize, 0));
            add_to_list(bp);
            coalesce(bp);
        }
        newptr = ptr;
    } else {
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
    }
    
    // check heap consistency
    //if (mm_check()) exit(1);

    return newptr;
}

static int mm_check() {
    void *bp;

    for (int i = 0; i < NUM_FREE_LISTS; i++) {
        for (bp = freelistp[i]; bp != NULL; bp = *NXTP(bp)) {
            // is every free block marked as free?
            if (GET_ALLOC(HDRP(bp))) {
                printf("There is an allocated block in the free list\n");
                return 1;
            }
            if (GET_ALLOC(FTRP(bp))) {
                printf("There is an allocated block in the free list\n");
                return 1;
            }
            
            // are there any contiguous free blocks?
            if (!GET_ALLOC(HDRP(PREV_BLKP(bp)))) {
                printf("There are contiguous free blocks %p (prev)\n", bp);
                return 1;
            }
            if (!GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {
                printf("There are contiguous free blocks %p (next)\n", bp);
                return 1;
            }
            
            // does every pointer point inside the heap
            if (*NXTP(bp) != NULL && 
                    (*NXTP(bp) < (void *)heap_listp || *NXTP(bp) > mem_heap_hi()))  {
                printf("There is a next pointer outside the heap\n");
                return 1;
            }
            if (*PRVP(bp) != NULL && 
                    (*PRVP(bp) < (void *)heap_listp || *PRVP(bp) > mem_heap_hi())) {
                printf("There is a prev pointer outside the heap\n");
                return 1;
            }
            
            // is every pointer pointing to a free block
            if (*NXTP(bp) != NULL && GET_ALLOC(HDRP(*NXTP(bp)))) {
                printf("A free block is pointing to an allocated block\n");
                return 1;
            }
            if (*PRVP(bp) != NULL && GET_ALLOC(HDRP(*PRVP(bp)))) {
                printf("A free block is pointing to an allocated block\n");
                return 1;
            }
            
         }
    }
    
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        // is every free block in the free list
        int is_in_free_list = 0;
        if (!GET_ALLOC(HDRP(bp))) {
            for (int i = 0; i < NUM_FREE_LISTS; i++)
                for (void *fbp = freelistp[i]; fbp != NULL; fbp = *NXTP(fbp))
                    if (bp == fbp) is_in_free_list = 1;

            if (!is_in_free_list) {
                printf("There is a free block not in the free list\n");
                return 1;
            }
        }
    }
    /*
    // print the state of the free lists
    int num_free_blocks[NUM_FREE_LISTS];
    
    for (int i = 0; i < NUM_FREE_LISTS; i++) {
        num_free_blocks[i] = 0;
    }
    
    for (int i = 0; i < NUM_FREE_LISTS; i++) {
        for (void *testbp = freelistp[i]; testbp != NULL; testbp = *NXTP(testbp)) {
            num_free_blocks[i]++;
	    }
    }
    
    for (int i = 0; i < NUM_FREE_LISTS; i++) {
        if (num_free_blocks[i])
            printf("%d %d;", i, num_free_blocks[i]);
    }
    printf("\n");
    
    
    // print the state of the heap
    for (void *bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        printf("%p %d %d;", bp, GET_SIZE(HDRP(bp))/4, GET_ALLOC(HDRP(bp)));
    }
    printf("\n");*/
    
    return 0;
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize) {
    int index = get_index(asize) - 2;
    if (index < 0) index = 0;
   
    void *bp = NULL;
    void *testbp;
    unsigned int size;
    
    for (int i = index; i < NUM_FREE_LISTS; i++) {
        if (i < 45) {
            testbp = freelistp[i];
            if (testbp == NULL) continue;
            
            size = GET_SIZE(HDRP(testbp));
            
            if (asize <= size) {
		        bp = testbp;
		        break;
		    }
		    
		    continue;
        }
        
        //int count = 0;
    
        for (testbp = freelistp[i]; testbp != NULL; testbp = *NXTP(testbp)) {
            size = GET_SIZE(HDRP(testbp));
            
            //count++;
            
            if (asize <= size) {
		        bp = testbp;
		        break;
		    }
	    }
	    //if (count > 0) printf("%d\n", count);
	    
	    if (bp) break;
    }
    
    return bp;
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
    
    // Adjust size downwards if the previous block was free
    //size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(mem_heap_hi())));
    //if (prev_alloc) {
    //    size -= GET_SIZE(HDRP(PREV_BLKP(mem_heap_hi())));
    //}
    
    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    add_to_list(bp);

    /* Coalesce if the previous block was free */
    void *coalesced_bp = coalesce(bp);
    
    //printf("Extending heap %d\n", words);
    //mm_check();
    
    return coalesced_bp;
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
        remove_from_list(bp);
        remove_from_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        add_to_list(bp);
    } else if (!prev_alloc && next_alloc) {
        // case 3: next is allocated, previous is not
        remove_from_list(bp);
        remove_from_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        add_to_list(bp);
    } else {
        // case 4: both prev and next are free
        remove_from_list(NEXT_BLKP(bp));
        remove_from_list(bp);
        remove_from_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        add_to_list(bp);
    }

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
        remove_from_list(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        // new free block
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
        add_to_list(bp);
    } else {
        // don't split case
        remove_from_list(bp);
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * add_to_list - add the given block to the free list
 */
static void add_to_list(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_index(size);

    // set new block as prev block of first
    if (freelistp[index] != NULL) PUT_ADDR(PRVP(freelistp[index]), bp);

    // set next block of bp to old first block
    PUT_ADDR(NXTP(bp), freelistp[index]);
    
    // set start of list to bp
    PUT_ADDR(PRVP(bp), NULL);
    freelistp[index] = (void *)(bp);
}

/*
 * remove_from_list - remove the given block from the free list
 */
static void remove_from_list(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_index(size);

    // remove from prev
    if (*PRVP(bp) != NULL) PUT_ADDR(NXTP(*PRVP(bp)), *NXTP(bp));
    
    // remove from next
    if (*NXTP(bp) != NULL) PUT_ADDR(PRVP(*NXTP(bp)), *PRVP(bp));
    
    // set start of list if needed
    if (bp == freelistp[index]) freelistp[index] = *NXTP(bp);
}

static int get_index(size_t size) {
    int index;

    // fixed bins for up to 512
    if (size < 512) index = size/8 - 1;
    else index = (int)(log2(1.0*size)) + 61;
    
    return index;
}
