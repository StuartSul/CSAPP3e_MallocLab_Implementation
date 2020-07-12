/*
 * mm.c - Implemented by Hyoung Uk Sul
 *
 * This implementation uses segregated free list to handle allocation and deallocation
 * of memory blocks. Furthermore, it utilizes the fact that given heap size is 20MB to use
 * int32_t value for header. That is, it uses 4 bytes to represent size and allocation flag.
 * Thereby, an allocated block will have 4-byte header followed by payload, and no footer.
 * A free block, on the other hand, will have 4 metadata: header, next free block, previous
 * free block, and footer. Except for header, this metadata use space allocated for payload. 
 * There is a routine, named prev_block, which checks if a block's footer is valid by checking
 * if it is a freed block. The following is an illustration of block structure.
 *
 *          ALLOCATED BLOCK                FREE BLOCK
 *         *****************            *****************
 *  4-Byte * SIZE/SET FLAG *     4-Byte * SIZE/SET FLAG *   (HEADER)
 *         *****************            *****************
 *         *               *     4-Byte * NEXT FREE BLK *
 *         *               *            *****************
 *         *               *     4-Byte * PREV FREE BLK *
 *         *               *            *****************
 *         *    PAYLOAD    *            *               *
 *         *               *            *    (EMPTY)    *
 *         *               *            *               *
 *         *               *            *****************
 *         *               *     4-Byte * SIZE/SET FLAG *   (FOOTER)
 *         *****************            *****************
 *
 * Segregated free list is always organized in ascending order, and allocation process will take
 * advantage of this to always find the best-fit for a newly allocated block. Freeing a memory will
 * always result in coalescing of memory whenever possible, and malloc and realloc function will always
 * try to allocate abundant amount of memory to prevent future external fragmentation.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"



/**********
 * Macros *
 **********/

/*
 * Constants
 */
#define ALIGNMENT   8               /* double word (8) alignment */
#define SIZEMASK   ~0x7             /* mask to retrieve size */
#define FLAGMASK    0x7             /* mask to retrieve allocated flag */
#define LIST_TOTAL  32              /* total number of segregated lists */
#define MALLOCBUF   1 << 12         /* minimum size of allocation */
#define REALLOCBUF  1 << 8          /* minimum additional size during reallocation */
#define HEADER_SIZE sizeof(int32_t) /* size of block header */

/*
 * Alignment Functions
 */
#define ALIGN(size)           (((size) + (ALIGNMENT-1)) & ~0x7)  /* align a size (unused; from original code) */
#define SIZE_T_SIZE           (ALIGN(sizeof(size_t)))            /* size_t size (unused; from original code) */
#define ALIGN_FOR_BLOCK(size) (((size) < ALIGNMENT) ? (ALIGNMENT << 1) : \
                              (((size) + HEADER_SIZE + ALIGNMENT - 1) & SIZEMASK)) /* align a size with header */

/*
 * Block Header-Related Functions
 */
#define BLOCK_SIZE(ptr)          (*(int32_t*)(ptr) & SIZEMASK)     /* retrieve block size (header + payload) */
#define PAYLOAD_SIZE(ptr)        (BLOCK_SIZE(ptr) - HEADER_SIZE)   /* retrieve payload size */
#define PAYLOAD_ADDR(ptr)        ((ptr) + HEADER_SIZE)             /* retrieve payload address from block address */
#define HEADER_ADDR(voidptr)     ((char*)(voidptr) - HEADER_SIZE)  /* retrieve block address from payload address */
#define SET_HEADER(ptr, size)    (*(int32_t*)(ptr) = (size) | 0x1) /* set and allocate header */
#define FREE_HEADER(ptr, size)   (*(int32_t*)(ptr) = (size)); \
                                 (*(int32_t*)((ptr) + (size) - HEADER_SIZE) = (size)) /* set and free header and footer */
#define NEXT_BLOCK(ptr)          ((ptr) + (*(int32_t*)(ptr) & SIZEMASK)) /* get next block in heap */
#define NEXT_LIST_HEADER(ptr)    ((ptr) + (HEADER_SIZE << 1))            /* get next segregated list head */
#define IS_SET(ptr)              ((*(int32_t*)(ptr) & FLAGMASK) == 0x1)  /* true if a block is marked allocated */

/*
 * Free List Related Functions
 */
#define NEXT_FREE_BLOCK_VAL(ptr)          (*(int32_t*)((ptr) + HEADER_SIZE))        /* get next free block value */
#define PREV_FREE_BLOCK_VAL(ptr)          (*(int32_t*)((ptr) + (HEADER_SIZE << 1))) /* get previous free block value */
#define SET_NEXT_FREE_BLOCK(ptr, nextptr) (NEXT_FREE_BLOCK_VAL(ptr) = (int32_t)((nextptr) - (ptr))) /* set next free block */
#define SET_PREV_FREE_BLOCK(ptr, prevptr) (PREV_FREE_BLOCK_VAL(ptr) = (int32_t)((prevptr) - (ptr))) /* set previous free block */
#define NEXT_FREE_BLOCK(ptr)              ((ptr) + NEXT_FREE_BLOCK_VAL(ptr))        /* get next free block pointer */
#define PREV_FREE_BLOCK(ptr)              ((ptr) + PREV_FREE_BLOCK_VAL(ptr))        /* get previous free block pointer */
#define IS_END(ptr)                       ((NEXT_FREE_BLOCK_VAL(ptr)) == 0)         /* true if reached end of free list */

/*
 * Heap Space Related Functions
 */ 
#define IS_WITHIN_HEAP(ptr)      ((ptr) <= (char*)mem_heap_hi())        /* true if a pointer does not exceed the heap */
#define GET_LAST_BLOCK_IF_FREE() (prev_block((char*)mem_heap_hi() + 1)) /* gets last block in heap, only if it is free */



/********************
 * Global Variables *
 ********************/

static char *head;  /* Points to the start of segregated free list heads */
static char *first; /* Points to the first allocated/freed block */



/********************
 * Function Headers *
 ********************/

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);
static void split_block(char *blkptr, int32_t newsize);
static char *prev_block(char *blkptr);
static char *search_free_list(int32_t size);
static void insert_into_list(char *blkptr);
static void remove_from_list(char *blkptr);
int mm_check(void);



/*******************************
 * Memory Management Functions *
 *******************************/

/* 
 * mm_init - Initialize the malloc package.
 *     Sets up segregated free list heads and extends heap by initial heap size.
 */
int mm_init(void)
{
    /* init_size - size that can contain all heads of segregated list, aligned */
    int32_t init_size = ((2 * HEADER_SIZE * LIST_TOTAL + HEADER_SIZE
                            + ALIGNMENT - 1) & SIZEMASK) - HEADER_SIZE;
    if ((head = (char*)mem_sbrk(init_size)) == (char*)-1)
        return -1;
    
    /* initialize segregated list */
    memset(head, 0, mem_heapsize());
    first = (char*)mem_heap_hi() + 1;

    /* allocate initial heap */
    mm_free(mm_malloc(MALLOCBUF));
    return 0;
}

/* 
 * mm_malloc - Allocate a block. First, round the requested size into nearest 2s power;
 *     then, search for segregated free block list for best-fit. If none, extend the heap
 *     by at least MALLOCBUF, and then allocate.
 */
void *mm_malloc(size_t size)
{
    if (size == 0)
        return NULL;

    /* if less than MALLOCBUF, round to nearest 2's power */
    if (size < MALLOCBUF) {
        int temp = 1;
        while (temp < size)
            temp <<= 1;
        size = temp;
    }

    char *list, *blkptr;
    int32_t newsize = ALIGN_FOR_BLOCK(size), bufsize;

    /* search segregated free list for available free blocks, starting at appropriate list, in ascending order */
    for (list = search_free_list(newsize); list <= first - ALIGNMENT; list = NEXT_LIST_HEADER(list)) {
        for (blkptr = NEXT_FREE_BLOCK(list);; blkptr = NEXT_FREE_BLOCK(blkptr)) {
            if (BLOCK_SIZE(blkptr) >= newsize) { /* found the best-fit */
                remove_from_list(blkptr);        /* remove this block from free list */
                split_block(blkptr, newsize);    /* split if the size is abundant */
                return (void*)PAYLOAD_ADDR(blkptr);
            } else if (IS_END(blkptr))
                break;
        }
    }

    /* there is no suitable free block; assign a new size that is at least MALLOCBUF */
    bufsize = newsize > MALLOCBUF ? newsize : MALLOCBUF;
    if ((blkptr = (char*)mem_sbrk(bufsize)) == (char*)-1)
        return NULL;
    FREE_HEADER(blkptr, bufsize); /* set header before allocating */
    split_block(blkptr, newsize); /* split if abundant */
    return (void*)PAYLOAD_ADDR(blkptr);
}

/*
 * mm_free - Free an allocated block. Given block is assumed to be allocated by this package.
 *      coalesce if previous or next block is free block as well; then insert into free block list
 */
void mm_free(void *ptr)
{
    if (ptr == NULL)
        return;

    char *blkptr = HEADER_ADDR(ptr);
    char *prevblkptr = prev_block(blkptr); /* NULL if previous block is not free */
    char *nextblkptr = NEXT_BLOCK(blkptr);
    int32_t size = BLOCK_SIZE(blkptr);

    /* coalesce if previous block is free */
    if (prevblkptr != NULL) {
        remove_from_list(prevblkptr); /* remove from free list */
        size += BLOCK_SIZE(prevblkptr);
        blkptr = prevblkptr;
    }

    /* coalesce if next block is free */
    if (IS_WITHIN_HEAP(nextblkptr) && !IS_SET(nextblkptr)) {
        remove_from_list(nextblkptr); /* remove from free list */
        size += BLOCK_SIZE(nextblkptr);
    }

    FREE_HEADER(blkptr, size);
    insert_into_list(blkptr); /* insert the new free block into segregated list */
    return;
}

/*
 * mm_realloc - Reallocate an allocated block. First, round the requested size into nearest 2s power;
 *     then, sees if given block can handle the new size. If so, return immediately; if not, see if
 *     coalescing with previous or next block can handle the new size. If so, coalesce, NOT split, and return.
 *     If not, sees if the given block is the last block in heap; if so, just extend heap by required additional
 *     size; if not, use mm_malloc and mm_free to allocate a completely new block.
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);
    else if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    /* if less than REALLOCBUF, round to nearest 2's power */
    if (size < REALLOCBUF) {
        int temp = 1;
        while (temp < size)
            temp <<= 1;
        size = temp;
    }

    char *blkptr = HEADER_ADDR(ptr);
    char *nextblkptr = NEXT_BLOCK(blkptr), *prevblkptr = prev_block(blkptr); /* NULL if previous block is not free */
    int32_t oldsize = BLOCK_SIZE(blkptr), newsize = ALIGN_FOR_BLOCK(size), combsize, bufsize;

    /* if rounded and aligned size fits within allocated memory, return as it is */
    if (newsize <= PAYLOAD_SIZE(blkptr)) 
        return ptr;
    
    /* check for different cases of reallocation */
    if (IS_WITHIN_HEAP(nextblkptr) && !IS_SET(nextblkptr) && 
            ((combsize = BLOCK_SIZE(nextblkptr) + oldsize) >= newsize)) {
        /* next block is free and combined size can contain the new size; coalesce and return */
        remove_from_list(nextblkptr);
        SET_HEADER(blkptr, combsize);
    } else if (IS_WITHIN_HEAP(nextblkptr) && !IS_SET(nextblkptr) && 
            prevblkptr != NULL && BLOCK_SIZE(prevblkptr) > REALLOCBUF &&
            ((combsize = BLOCK_SIZE(prevblkptr) + oldsize + BLOCK_SIZE(nextblkptr)) >= newsize)) {
        /* previous block and next block are free, they can altogether contain the new size, and */
        /* the previous block is at least as large as REALLOCBUF; coalesce and return            */
        remove_from_list(prevblkptr);
        remove_from_list(nextblkptr);
        memmove(prevblkptr, blkptr, oldsize); /* using memmove for safety over overlapping memory */
        blkptr = prevblkptr;
        SET_HEADER(blkptr, combsize);
    } else if (prevblkptr != NULL && (BLOCK_SIZE(prevblkptr) > REALLOCBUF) &&
            ((combsize = BLOCK_SIZE(prevblkptr) + oldsize) >= newsize)) {
        /* previous block is free, the combined size can contain the new size, and the previous block */
        /* is at least as REALLOCBUF (to prevent further external fragmentation); coalesce and return */
        remove_from_list(prevblkptr);
        memmove(prevblkptr, blkptr, oldsize); /* using memmove for safety over overlapping memory */
        blkptr = prevblkptr;
        SET_HEADER(blkptr, combsize);
    } else if (!IS_WITHIN_HEAP(nextblkptr)) {
        /* none of above case holds, but the given block is the last block in memory */
        bufsize = ALIGN_FOR_BLOCK(newsize - oldsize);
        if (mem_sbrk(bufsize) == (void*)-1)
            return NULL;
        SET_HEADER(blkptr, oldsize + bufsize);
    } else {
        /* none of above case holds; just allocate a memory block */
        if ((nextblkptr = (char*)mm_malloc(newsize)) == NULL)
            return NULL;
        memcpy(nextblkptr, ptr, PAYLOAD_SIZE(blkptr));
        mm_free(ptr);
        blkptr = HEADER_ADDR(nextblkptr);
    }
    return (void*)PAYLOAD_ADDR(blkptr);
}



/********************
 * Helper Functions *
 ********************/

 /*
  * split_block - Allocate a free block with new size, and split if abundant
  */
static void split_block(char *blkptr, int32_t newsize) {
    char *newblkptr;
    int32_t oldsize = BLOCK_SIZE(blkptr);
    if (newsize < oldsize - ALIGNMENT) { /* there is enough space to split the block */
        SET_HEADER(blkptr, newsize);
        newblkptr = NEXT_BLOCK(blkptr);
        FREE_HEADER(newblkptr, oldsize - newsize); /* set header for split block */
        insert_into_list(newblkptr);     /* insert split block into segregated list */
    } else                               /* this block cannot be split */
        SET_HEADER(blkptr, oldsize);
}

/*
 * prev_block - Return the previous block if it is free; NULL otherwise.
 */
static char *prev_block(char *blkptr)
{
    char *list;
    char *tempblkptr;
    char *prevblk_footer = blkptr - HEADER_SIZE;
    char *prevblk_header = blkptr - BLOCK_SIZE(prevblk_footer);

    /* prevblk_footer and prevblk_header are retrieved assuming that the previous block to         */
    /* blkptr is a free block; that is, it contains a footer information. Now, it must be checked  */
    /* whether this assumption is true: is the previous block free? is previous block within heap? */
    /* is previous block header and footer appropriately distanced? is the previous block header   */
    /* abiding by alignment requirement? is the header and the footer contain same data?           */
    /* checking in that order, returning NULL if any of conditions not hold                        */
    if (IS_SET(prevblk_footer) ||
        prevblk_header < first ||
        prevblk_header > prevblk_footer - HEADER_SIZE * 3 ||
        (uint32_t)(prevblk_header + HEADER_SIZE) % ALIGNMENT != 0 ||
        BLOCK_SIZE(prevblk_header) != BLOCK_SIZE(prevblk_footer) ||
        IS_SET(prevblk_header))
        return NULL;
    
    /* finally, check if the block is officially a free block by looking into segregated list */
    list = search_free_list(BLOCK_SIZE(prevblk_header));
    for (tempblkptr = NEXT_FREE_BLOCK(list);; tempblkptr = NEXT_FREE_BLOCK(tempblkptr)) {
        if (prevblk_header == tempblkptr)
            return prevblk_header; /* block exists in free list; return the block */
        else if (IS_END(tempblkptr))
            break;
    }

    return NULL;
}

/*
 * search_free_list - Returns head to a free list among segregated lists that best-fits given size
 */
static char *search_free_list(int32_t size) 
{   
    char *list = head;
    int order = size >> 4;
    int list_num = 1;

    /* repeat until given size fits within range defined by "order." Order will begin at 16,   */
    /* and increase exponentially; if size overfits any of the order, go to the very last list */
    while (order > 1 && list_num < LIST_TOTAL) {
        order >>= 1;
        list_num++;
        list = NEXT_LIST_HEADER(list);
    }
    return list;
}

/*
 * insert_into_list - Inserts a new free block into free list, in ascending order.
 */
static void insert_into_list(char *blkptr)
{
    /* first, find the list that best-fits block's size */
    char *list = search_free_list(BLOCK_SIZE(blkptr));

    /* if there is a free block in this list, insert by ascending order */
    if (!IS_END(list)) {
        while (1) {
            /* insert when the block not greater than next block, or */
            /* there is no more block in the list                    */
            if (BLOCK_SIZE(NEXT_FREE_BLOCK(list)) >= BLOCK_SIZE(blkptr)) {
                /* found the appropriate position */
                SET_NEXT_FREE_BLOCK(blkptr, NEXT_FREE_BLOCK(list));
                SET_PREV_FREE_BLOCK(NEXT_FREE_BLOCK(list), blkptr);
                SET_NEXT_FREE_BLOCK(list, blkptr);
                SET_PREV_FREE_BLOCK(blkptr, list);
                return;
            } else if (IS_END(NEXT_FREE_BLOCK(list))) {
                /* there is no more block to compare to */
                SET_NEXT_FREE_BLOCK(NEXT_FREE_BLOCK(list), blkptr);
                SET_NEXT_FREE_BLOCK(blkptr, blkptr);
                SET_PREV_FREE_BLOCK(blkptr, NEXT_FREE_BLOCK(list));
                return;
            }
            /* none of above condition holds; go to next item in the list */
            list = NEXT_FREE_BLOCK(list);
        }
    } else { /* there is no free block in this list; just insert as its first item */
        SET_NEXT_FREE_BLOCK(list, blkptr);
        SET_NEXT_FREE_BLOCK(blkptr, blkptr);
        SET_PREV_FREE_BLOCK(blkptr, list);
        return;
    }
}

/*
 * remove_from_list - Removes a free block from free list.
 */
static void remove_from_list(char *blkptr)
{
    char *prevblkptr = PREV_FREE_BLOCK(blkptr);
    char *nextblkptr = NEXT_FREE_BLOCK(blkptr);
    if (IS_END(blkptr)) /* if at the end of free list, just fix the previous block */
        SET_NEXT_FREE_BLOCK(prevblkptr, prevblkptr);
    else { /* if in the middle of free list, connect previous and next free blocks */
        SET_NEXT_FREE_BLOCK(prevblkptr, nextblkptr);
        SET_PREV_FREE_BLOCK(nextblkptr, prevblkptr);
    }
    return;
}



/***************************
 * Heap Consistency Cheker *
 ***************************/

/*
 * mm_check - Checks for heap consistency. Returns 0 if inconsistent, and 1 otherwise.
 */
int mm_check(void)
{
    /*
     * Options - Change these values to check for different cases
     */
    int verbose = 1;                     /* print the results */
    int printAllBlocks = 0;              /* print all blocks */
    int printFreeList = 0;               /* print all free lists */
    int checkFreeListMarks = 1;          /* check if blocks in free list are marked free */
    int checkFreeBlockCoalesce = 1;      /* check if every continuous free blocks are coalesced */
    int checkAllFreeBlockInFreeList = 1; /* check if every free block is in free list */
    int checkFreeBlockFooter = 1;        /* check if free blocks have appropriate footers */
    int checkOverlap = 1;                /* check if any of blocks overlap */
    int checkWithinHeap = 1;             /* check if every block is within heap */
    /*
     * End of options
     */

    if (verbose)
	    printf("\n**mm_check initiated**\n");

    char *blkptr, *list, *tempblk, *templist;
    int i, j;

    /* print all blocks that are allocated/freed within heap */
    if (printAllBlocks) {
        i = 1;
        j = 1;
        if (verbose)
            printf("\n\n\n____________________ALL BLOCKS_______________________\n");
        for (blkptr = first; blkptr < (char*)mem_heap_hi(); blkptr = NEXT_BLOCK(blkptr)) {
            if (verbose)
                printf("Block #%d: [%p] %d Bytes (%s)\n", 
                    i++, blkptr, BLOCK_SIZE(blkptr), IS_SET(blkptr) ? "Set" : "FREE");
        }
    }

    /* print all free lists; this code prints the head itself when list is empty */
    if (printFreeList) {
        i = 1;
        j = 1;
        if (verbose)
            printf("\n\n____________________FREE LISTS_______________________\n\n");
        for (list = head; list <= first - ALIGNMENT; list = NEXT_LIST_HEADER(list)) {
            if (verbose)
                printf("LIST %d[%p]:\n", i++, list);
            for (blkptr = NEXT_FREE_BLOCK(list);; blkptr = NEXT_FREE_BLOCK(blkptr)) {
                if (verbose)
                    printf("  Block #%d: [%p] %d Bytes (%s)\n", 
                        j++, blkptr, BLOCK_SIZE(blkptr), IS_SET(blkptr) ? "Set" : "FREE");
                if (IS_END(blkptr))
                    break;
            }
            j = 1;
        }
    }

    /* check if every free block in segregated free block list are marked free in its header */
	if (checkFreeListMarks) {
        list = head;
        for (i = 0; i < LIST_TOTAL; i++) {
            if (!IS_END(list)) {
                for (blkptr = NEXT_FREE_BLOCK(list);; blkptr = NEXT_FREE_BLOCK(blkptr)) {
                    if (IS_SET(blkptr)){ /* there is a block in free list that is marked allocated */
                        if (verbose)
                            printf("checkFreeListMarks failed\n");
                        return 0;
                    }
                    if (IS_END(blkptr))
                        break;
                }
            }
            list = NEXT_LIST_HEADER(list); /* look into next list */
        }
        if (verbose)
            printf("checkFreeListMarks passed\n");
    }

    /* check if there exist any cases of continuous free blocks */
    if (checkFreeBlockCoalesce) {
        for (blkptr = first; IS_WITHIN_HEAP(blkptr); blkptr = NEXT_BLOCK(blkptr)) {
            if (IS_WITHIN_HEAP(NEXT_BLOCK(blkptr)) && !IS_SET(blkptr) && !IS_SET(NEXT_BLOCK(blkptr))) {
                /* there is a consecutive sequence of free blocks */
                if (verbose)
                    printf("checkFreeBlockCoalesce failed\n");
                return 0;
            }
        }
        if (verbose)
            printf("checkFreeBlockCoalesce passed\n");
    }

    /* check if every free block is in fact in the free list */
    if (checkAllFreeBlockInFreeList) {
        list = head;
        for (i = 0; i < LIST_TOTAL; i++) {
            for (blkptr = first; IS_WITHIN_HEAP(blkptr); blkptr = NEXT_BLOCK(blkptr)) {
                if (!IS_SET(blkptr)) {
                    templist = search_free_list(BLOCK_SIZE(blkptr)); /* search for free list that this block belongs to */
                    for (tempblk = NEXT_FREE_BLOCK(templist);; tempblk = NEXT_FREE_BLOCK(tempblk)) {
                        if (blkptr == tempblk) /* block is in the free list; no error */
                            break;
                        else if (IS_END(tempblk)) { /* block is not in the free list */
                            if (verbose)
                                printf("checkAllFreeBlockInFreeList failed\n");
                            return 0;
                        }
                    }
                }
            }
        }
        if (verbose)
            printf("checkAllFreeBlockInFreeList passed\n");
    }

    /* check if every free block has good footer (only free blocks have footer in this implementation) */
    if (checkFreeBlockFooter) {
        list = head;
        for (i = 0; i < LIST_TOTAL; i++) {
            for (blkptr = first; IS_WITHIN_HEAP(blkptr); blkptr = NEXT_BLOCK(blkptr)) {
                if (!IS_SET(blkptr)) {
                    tempblk = blkptr + BLOCK_SIZE(blkptr) - HEADER_SIZE; /* get footer */
                    if (IS_SET(tempblk) || BLOCK_SIZE(tempblk) != BLOCK_SIZE(blkptr)) { 
                        /* is not marked free, or does not contain right size */
                        if (verbose)
                            printf("checkFreeBlockFooter failed\n");
                        return 0;
                    }
                }
            }
        }
        if (verbose)
            printf("checkFreeBlockFooter passed\n");
    }

    /* check if no blocks overlap in the heap; THIS DOES NOT CHECK every case of overlap as it is done by mdriver */
    if (checkOverlap) {
        for (blkptr = first; IS_WITHIN_HEAP(blkptr); blkptr = NEXT_BLOCK(blkptr)) {
            if (IS_WITHIN_HEAP(NEXT_BLOCK(blkptr)) && NEXT_BLOCK(blkptr) < blkptr + HEADER_SIZE * 3) {
                /* this block is not the last block in heap, yet the next block position is awkward */
                if (verbose)
                    printf("checkOverlap failed\n");
                return 0;
            }
        }
        if (verbose)
            printf("checkOverlap passed.\n");
    }

    /* check if every block is within heap */
	if (checkWithinHeap) {
        for (blkptr = first; IS_WITHIN_HEAP(blkptr); blkptr = NEXT_BLOCK(blkptr));
        if (blkptr != (char*)mem_heap_hi() + 1) {
            /* swiped through all the blocks until it exceeds heap, yet the destination position is awkward */
            if (verbose)
                printf("checkWithinHeap failed\n");
            return 0;
        }
        if (verbose)
            printf("checkWithinHeap passed.\n");
    }

    /* passed every condition checker in this function */
    if (verbose)
	    printf("**mm_check has found no error**\n\n");
    return 1;
}