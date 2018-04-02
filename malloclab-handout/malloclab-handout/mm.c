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
/*
 *******************************
 *HEAD                        a*
 *******************************
 *PRED                         *
 *******************************
 *SUCC                         *
 *******************************
 *CONTENT                      *
 *******************************
 *PADDING                      *
 *******************************
 *FOOT                        a*
 *******************************
*/
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
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
    "sixsixsix",
    /* First member's full name */
    "Huppert Wu",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};


/*
 * If NEXT_FIT defined use next fit search, else use first-fit search 
 */

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp
/* $end mallocmacros */

#define NEXT_PTR(p)   (*(char **)(p))
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define PUT_ADDR(p,q) (*(char**)(p)= (char*)(q))



static char * freelist;
static char *heap_listp = 0;  /* Pointer to first block */  


static void printblock(void *bp); 
void checkheap(int verbose);
void checkblock(void *bp);


static int position(size_t size);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static int insert2list(void *bp);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void Removechunk(void *bp);
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    void * ptr;
        /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(24*WSIZE)) == (void *)-1) //line:vm:mm:begininit
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(11*DSIZE, 1)); /* Prologue header */ 
    for (int x = 2;  x <= 21; x++)
    {

        ptr = heap_listp+(x*WSIZE);
        if (x%2 == 0)
        {
            PUT_ADDR(ptr,ptr+WSIZE);
        }
        else
        {
            PUT_ADDR(ptr,ptr-WSIZE);
        }
    }
    freelist = heap_listp+(2*WSIZE);

    PUT(heap_listp + (22*WSIZE), PACK(11*DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (23*WSIZE), PACK(0, 1));     /* Epilogue header */

    heap_listp += (2*WSIZE);                     //line:vm:mm:endinit  
    /* $end mminit */

    /* $begin mminit */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;

}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *bp;

    /* $end mmmalloc */
    if (heap_listp == 0){
        mm_init();
    }
    /* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          //line:vm:mm:sizeadjust1
        asize = 2*DSIZE;                                        //line:vm:mm:sizeadjust2
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); //line:vm:mm:sizeadjust3

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  //line:vm:mm:findfitcall
        place(bp, asize);                  //line:vm:mm:findfitplace
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 //line:vm:mm:growheap1
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  //line:vm:mm:growheap2
    place(bp, asize);                                 //line:vm:mm:growheap3
    return bp;

}
/* $end mmmalloc */
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr),PACK(size,0));
    PUT(FTRP(ptr),PACK(size,0));
    insert2list(coalesce(ptr));

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    size_t asize;
    void *newptr;
    int predalloc,succalloc,totalsize;
    void * predbp;
    void * succbp;
    void * tempbp;
    predbp = PREV_BLKP(ptr);
    succbp = NEXT_BLKP(ptr);
    predalloc = GET_ALLOC(HDRP(predbp));
    succalloc = GET_ALLOC(HDRP(succbp));


    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    /*alignment*/
    asize = DSIZE*((size+DSIZE-1)/DSIZE);

    oldsize = GET_SIZE(HDRP(ptr));

    if((!predalloc) && ((GET_SIZE(HDRP(predbp)) + oldsize - DSIZE) >= asize))
    {
        totalsize = GET_SIZE(HDRP(predbp)) + oldsize;
        Removechunk(PREV_BLKP(ptr));
        //size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(totalsize, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(totalsize, 0));
        newptr = PREV_BLKP(ptr);
        memmove(newptr,ptr,size);
    }
    else if ((!succalloc) && ((GET_SIZE(HDRP(succbp)) + oldsize - DSIZE) >= asize) )
    {
        totalsize = GET_SIZE(HDRP(succbp)) + oldsize;
        Removechunk(NEXT_BLKP(ptr));
        //size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(totalsize, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(totalsize,0));
        newptr = ptr;
        memmove(newptr,ptr,size);
    }
    else if ((!predalloc) && (!succalloc) && ((GET_SIZE(HDRP(predbp)) + GET_SIZE(HDRP(succbp)) + oldsize - DSIZE) >= asize))
    {
        totalsize = GET_SIZE(HDRP(predbp)) + GET_SIZE(HDRP(succbp)) + oldsize;
        newptr = coalesce(ptr);
        memmove(newptr,ptr,size);
    }
    else
    {
        newptr = mm_malloc(size);
        /* If realloc() fails the original block is left untouched  */
        if(!newptr) {
            return 0;
        }
         /* Copy the old data. */
        if(size < oldsize)
            oldsize = size;
        memcpy(newptr, ptr, oldsize);

        /* Free the old block. */
        mm_free(ptr);
        return newptr;


    }

    if((totalsize - DSIZE - asize) >= 2*DSIZE)
    {
        PUT(HDRP(newptr),PACK(asize+DSIZE,1));
        PUT(FTRP(newptr),PACK(asize+DSIZE,1));
        tempbp = NEXT_BLKP(newptr);
        PUT(HDRP(tempbp),PACK(totalsize - DSIZE - asize,0));
        PUT(FTRP(tempbp),PACK(totalsize - DSIZE - asize,0));
        insert2list(tempbp);
        return newptr;
    }
    else
    {
        PUT(HDRP(newptr),PACK(totalsize,1));
        PUT(FTRP(newptr),PACK(totalsize,1));
        return newptr;
    }

   //return newptr;
}



static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; //line:vm:mm:beginextend
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        //line:vm:mm:endextend

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   //line:vm:mm:freeblockhdr
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   //line:vm:mm:freeblockftr
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ //line:vm:mm:newepihdr

    /* Coalesce if the previous block was free */
    bp = coalesce(bp);
    insert2list(bp);
    return bp;                                          //line:vm:mm:returnblock
}

static void *coalesce(void *bp)
{

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */

        Removechunk(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */

        Removechunk(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

    }

    else {                                     /* Case 4 */

        Removechunk(NEXT_BLKP(bp));
        Removechunk(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;

}
static int insert2list(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    size_t asize = position(size);
    void * fdptr;
    void * bkptr;
    void * pred;
    void * succ;

    if (asize >= 13)
        pred = freelist + (18*WSIZE);
    else
        pred = freelist + (asize - 4)*2*WSIZE;


    succ = pred+ WSIZE;
    bkptr = bp;
    fdptr = bkptr + WSIZE;

    /*change succ,pred last*/
    PUT_ADDR(fdptr,NEXT_PTR(succ));
    PUT_ADDR(bkptr, succ);
    PUT_ADDR(NEXT_PTR(succ),fdptr);
    PUT_ADDR(succ, bkptr);


    return 1;
}
static int position(size_t size)
{
    int x = 0;
    x += (!!(size>>(16+x)))<<4;
    x += (!!(size>>(8+x)))<<3;
    x += (!!(size>>(4+x)))<<2;
    x += (!!(size>>(2+x)))<<1;
    x += (!!(size>>(1+x)));
    return (!!(size&(~(1<<x)))+x);


}


static void *find_fit(size_t asize)
{
    size_t rsize = position(asize);
    /* $begin mmfirstfit */

    /* First-fit search */
    void *bp;
    void *horbp;
    void *verbp;
    if (rsize>=13)
        bp = freelist + 9*2*WSIZE;
    else
        bp = freelist+((rsize-4)*2*WSIZE);
    horbp = bp;
    while (horbp != (freelist+20*WSIZE)) 
    {

        verbp = NEXT_PTR(horbp + WSIZE);
        while (verbp != horbp)
        {
            if ((asize <= GET_SIZE(HDRP(verbp)))) 
            {
                return verbp;
            }
            verbp = NEXT_PTR(verbp+WSIZE);
        }
        horbp = horbp + DSIZE;
    }

    return NULL; /* No fit */
}


static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    void * curbp = bp;

    Removechunk(curbp);
    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(curbp), PACK(asize, 1));
        PUT(FTRP(curbp), PACK(asize, 1));

        curbp = NEXT_BLKP(curbp);
        PUT(HDRP(curbp), PACK(csize-asize, 0));
        PUT(FTRP(curbp), PACK(csize-asize, 0));

        insert2list(coalesce(curbp));
    }
    else { 

        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void Removechunk(void *bp)
{

    void * succ = NEXT_PTR(bp);
    void * bkptr = NEXT_PTR(bp+WSIZE);

    PUT_ADDR(bkptr,succ);
    PUT_ADDR(succ,bkptr);
    return;

}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}


void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */
void checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}

void mm_checkheap(int verbose)  
{ 
    checkheap(verbose);
}
