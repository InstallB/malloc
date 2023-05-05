/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */

// Implicit free list
// block: head(4B) + payload + tail(4B), header == tail, [29]size + '00' + [1]free
// linked list
// try first fit

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

// below are my definitions
#define SINGLEWORD 4
#define DOUBLEWORD 8

#define GETVAL(p) (*((unsigned int*)(p))) // get value
#define SETVAL(p,v) ((*((unsigned int*)(p))) = (v)) // set value

#define GET_SIZE(p) ((GETVAL(p)) & (~0x7)) // size of block
#define GET_ALLOC(p) ((GETVAL(p)) & (0x1)) // whether block is allocated

unsigned char* extend_heap(size_t size){
    unsigned char *p = mem_sbrk(size + DOUBLEWORD);
    if((long)p < 0) return NULL;
    unsigned char *q = mem_heap_hi() - (SINGLEWORD - 1);
    // printf("extend %p %p %lu\n",p,q,size);
    SETVAL(q,0 | 1); // set new TAIL block

    SETVAL(p - SINGLEWORD,size | 0); // new block head
    SETVAL(q - SINGLEWORD,size | 0); // new block tail
    return p - SINGLEWORD;
}

unsigned char* first_fit(size_t size){
    // printf("FIRST_FIT\n");
    unsigned char *p = mem_heap_lo();
    p += SINGLEWORD; // head of HEADER block
    while(p < (unsigned char*)(mem_heap_hi())){
        if(!GET_ALLOC(p) && GET_SIZE(p) >= size) return p;
        p += (GET_SIZE(p) + DOUBLEWORD);
    } // scan head of every block
    return NULL;
}

void place_block(unsigned char* p,size_t size){ // p is start of BLOCK
    // printf("PLACE_BLOCK\n");
    size_t block_size = GET_SIZE(p);
    SETVAL(p,size | 1); // set head
    SETVAL(p + size + SINGLEWORD,size | 1); // set tail

    if(block_size > size){
        unsigned char *q = p + size + DOUBLEWORD; // head of split block
        size_t split_size = block_size - size - DOUBLEWORD; // size of new splitted block(need to -8!!!!)
        // printf("SPLIT %p %lu %lu %lu\n",p,size,block_size,split_size);
        SETVAL(q - SINGLEWORD,size | 1); // tail of block
        SETVAL(q,split_size | 0); // head of split block
        SETVAL(q + split_size + SINGLEWORD,split_size | 0); // tail of split block
    } // SPLIT BLOCK
}

void merge_block(unsigned char* p,size_t size){ // p is start of BLOCK
    size_t las_size = GET_SIZE(p - SINGLEWORD);
    int las_alloc = GET_ALLOC(p - SINGLEWORD);
    size_t nxt_size = GET_SIZE(p + size + DOUBLEWORD);
    int nxt_alloc = GET_ALLOC(p + size + DOUBLEWORD);
    size_t new_size;
    unsigned char *q;
    // printf("MERGE_BLOCK %d %d\n",las_alloc,nxt_alloc);

    if(las_alloc && nxt_alloc) return;

    else if(!las_alloc && nxt_alloc){
        new_size = las_size + DOUBLEWORD + size;
        q = p - las_size - DOUBLEWORD; // startpos of merged block
    }

    else if(las_alloc && !nxt_alloc){
        new_size = size + DOUBLEWORD + nxt_size;
        q = p;
    }

    else{
        new_size = las_size + DOUBLEWORD + size + DOUBLEWORD + nxt_size;
        q = p - las_size - DOUBLEWORD;
        // printf("%p %p %lu %lu %lu %lu\n",p,q,las_size,size,nxt_size,new_size);
    }

    SETVAL(q,new_size | 0); // head
    SETVAL(q + new_size + SINGLEWORD,new_size | 0); // tail
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void){
    mem_sbrk(SINGLEWORD); // used for alignment

    unsigned char *p = mem_sbrk(DOUBLEWORD); // ADD HEADER : VIEW AS ALLOCATED SIZE=8 BLOCK
    if((long)p < 0) return -1;
    SETVAL(p,0 | 1); // head of HEADER
    SETVAL(p + SINGLEWORD,0 | 1); // tail of HEADER

    p = mem_sbrk(SINGLEWORD); // ADD TAIL
    if((long)p < 0) return -1;
    SETVAL(p,0 | 1);
    // mm_checkheap(0);
    return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size){
    size = (size + 7) & (~0x7);
    unsigned char *p = first_fit(size);
    if(p == NULL) p = extend_heap(size);

    // printf("MALLOC %p\n",p);

    if(p == NULL){
        return NULL;
        // malloc failed
    }

    place_block(p,size);
    // mm_checkheap(1);
    // here p is the address of head of BLOCK, so returnvalue have to +4
    return p + SINGLEWORD;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr){

    // printf("FREE %p\n",ptr);

    if(ptr == NULL) return;
    size_t size = GET_SIZE(ptr - SINGLEWORD);
    int allocated_ = GET_ALLOC(ptr - SINGLEWORD);
    if(!allocated_) return;
    SETVAL(ptr - SINGLEWORD,size | 0); // set head
    SETVAL(ptr + size,size | 0); // set tail
    merge_block(ptr - SINGLEWORD,size);
    // mm_checkheap(2);
/*Get gcc to be quiet */
    // ptr = ptr;
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 */
void *realloc(void *oldptr, size_t size){
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0){
        free(oldptr);
        return NULL;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) return malloc(size);

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) return NULL;

    /* Copy the old data. */
    oldsize = *SIZE_PTR(oldptr);
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);

    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size){
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr,0,bytes);

    return newptr;
}

/*
    I hate my life.
    I HATE MY LIFE.
*/
void mm_checkheap(int verbose){
    verbose = verbose;
    unsigned char *p = mem_heap_lo();
    p += SINGLEWORD; // head of HEADER block
    printf("CHECKHEAP: %p %p: ",p,mem_heap_hi());
    int las = 1,flg = 0;
    while(p < (unsigned char*)(mem_heap_hi())){
        // printf("%p,%u,%u ",p,GET_SIZE(p),GET_ALLOC(p));
        if(!las && !GET_ALLOC(p)){
            printf("ERROR NOTMERGED : %d\n",verbose);
            // assert(0);
            flg = 1;
        }
        if(GET_SIZE(p) > 0 && GETVAL(p) != GETVAL(p + GET_SIZE(p) + SINGLEWORD)){
            printf("ERROR HEADTAILNOTEQUAL : %d %u %u\n",verbose,GETVAL(p),GETVAL(p + GET_SIZE(p) + SINGLEWORD));
            // assert(0);
            flg = 1;
        }
        las = GET_ALLOC(p);
        p += (GET_SIZE(p) + DOUBLEWORD);
    }
    if(flg) assert(0);
    printf("\n");
}
