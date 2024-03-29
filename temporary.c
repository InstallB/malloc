// 参考了文章，但没参考代码：https://zhuanlan.zhihu.com/p/496366818

// Segregated Free Lists
// block: [head(4B) + pre(4B) + nxt(4B) + payload + tail(4B)], header == tail, [29]size + '00' + [1]free
// K doubly-linked lists
// 每次在头插入/删除，malloc O(1)
// 合并的时候不用管链表直接看堆前后，然后插入删除还是 O(1)
// really impressive algorithm.

// 用 lo() + 偏移量，这样指针用 32 位整数存，只要 4B。

// 最小的块要 16B
// 分 K 组，[2^4,2^5),[2^5,2^6),...[2^(K+3),inf) 为一组，设置头指针。
// 如果偏移量值为 0 就视为指针是 NULL

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
#define MIN(x,y) ((x) < (y) ? (x) : (y))
#define MAX(x,y) ((x) > (y) ? (x) : (y))

#define CATEGORY 24 // [0,K)
#define CATEGORY_MINSIZE(x) (1u << ((x) + 4)) // including 16B extra information
#define CATEGORY_MAXSIZE(x) ((1u << ((x) + 5)) - 1)
#define GET_CATEGORY(x) MIN(CATEGORY - 1,27 - __builtin_clz((x) + EXTRA)) // x should be unsigned int, x is **PAYLOAD** size, returns the category id x belongs to

#define LINKLIST_HEAD(x) (((unsigned char *)(mem_heap_lo())) + (4 * (x))) // head of linklist of category x, returns unsigned char*
#define DELTA(p) (((unsigned char *)(p)) - ((unsigned char *)(mem_heap_lo()))) // returns unsigned int
#define GETP(delta) (((unsigned char *)(mem_heap_lo())) + (delta)) // returns unsigned char*

#define SINGLEWORD 4
#define DOUBLEWORD 8
#define HEADER 12
#define EXTRA 16

#define GETVAL(p) (*((unsigned int*)(p))) // p is start of block (head), get value
#define SETVAL(p,v) ((*((unsigned int*)(p))) = (v)) // p is start of block (head), set value

#define GET_SIZE(p) ((GETVAL(p)) & (~0x7)) // p is start of block (head), get size of block
#define GET_ALLOC(p) ((GETVAL(p)) & (0x1)) // p is start of block (head), whether block is allocated

// below are linklist operations
#define SETPRE(p,v) SETVAL(((p) + SINGLEWORD),(v)) // p is start of block (head), v is delta value (unsigned int)
#define SETNXT(p,v) SETVAL(((p) + DOUBLEWORD),(v)) // p is start of block (head), v is delta value (unsigned int)

void linklist_inserthead(int cat,unsigned char* p){ // p is beginnning of block
    // insert p to the head of cat-th linklist
    if(!cat) return;
    size_t delta_nxt = GETVAL(LINKLIST_HEAD(cat));
    SETPRE(p,0);
    SETNXT(p,0);
    if(delta_nxt != 0){
        unsigned char *q = GETP(delta_nxt);
        SETNXT(p,DELTA(q));
        SETPRE(q,DELTA(p));
    }
    SETVAL(LINKLIST_HEAD(cat),DELTA(p));
}

void linklist_remove(int cat,unsigned char* p){ // p is beginnning of removed block
    if(!cat) return;
    unsigned char *pre = NULL,*nxt = NULL;
    size_t delta_pre = GETVAL(p + SINGLEWORD);
    size_t delta_nxt = GETVAL(p + DOUBLEWORD);
    if(delta_pre != 0) pre = GETP(delta_pre);
    if(delta_nxt != 0) nxt = GETP(delta_nxt);

    if(pre != NULL && nxt != NULL){
        SETPRE(nxt,DELTA(pre));
        SETNXT(pre,DELTA(nxt));
    }
    else if(pre == NULL && nxt != NULL){
        SETPRE(nxt,0);
        SETVAL(LINKLIST_HEAD(cat),DELTA(nxt));
    }
    else if(pre != NULL && nxt == NULL){
        SETNXT(pre,0);
    }
    else{
        SETVAL(LINKLIST_HEAD(cat),0);
    }
}

unsigned char* extend_heap(size_t size){
    unsigned char *p = mem_sbrk(size + EXTRA);
    if((long)p < 0) return NULL;
    unsigned char *q = mem_heap_hi() - (SINGLEWORD - 1); // beginning of last '4B'
    // printf("extend %p %p %lu\n",p,q,size);
    SETVAL(q,0 | 1); // set new TAIL block

    SETVAL(p - SINGLEWORD,size | 1); // new block head
    SETVAL(q - SINGLEWORD,size | 1); // new block tail
    return p - SINGLEWORD;
}

void place_block(unsigned char* p,size_t size){ // p is start of BLOCK
    size_t block_size = GET_SIZE(p);
    int block_cat = GET_CATEGORY(block_size);
    linklist_remove(block_cat,p);
    // printf("PLACE_BLOCK %lu %lu %p\n",size,block_size,p);
    assert(block_size >= size);

    if(block_size == size + EXTRA) size = block_size;

    SETVAL(p,size | 1); // set head
    SETVAL(p + size + HEADER,size | 1); // set tail

    if(block_size > size){
        assert(block_size >= size + EXTRA);
        unsigned char *q = p + size + EXTRA; // head of split block
        size_t split_size = block_size - size - EXTRA; // size of new splitted block (need to -EXTRA!!!)
        int split_cat = GET_CATEGORY(split_size);

        SETVAL(q,split_size | 0); // head of split block
        SETVAL(q + split_size + HEADER,split_size | 0); // tail of split block
        linklist_inserthead(split_cat,q);
    } // SPLIT BLOCK
}

void merge_block(unsigned char* p,size_t size){ // p is start of BLOCK
    size_t las_size = GET_SIZE(p - SINGLEWORD);
    int las_cat = GET_CATEGORY(las_size);
    int las_alloc = GET_ALLOC(p - SINGLEWORD);
    size_t nxt_size = GET_SIZE(p + size + EXTRA);
    int nxt_cat = GET_CATEGORY(nxt_size);
    int nxt_alloc = GET_ALLOC(p + size + EXTRA);
    size_t new_size;
    int new_cat;
    unsigned char *q; // startpos of new unallocated block

    // printf("MERGE_BLOCK %d %d\n",las_alloc,nxt_alloc);

    if(las_alloc && nxt_alloc){
        new_size = size;
        q = p;
    }
    else if(!las_alloc && nxt_alloc){
        new_size = las_size + EXTRA + size;
        q = p - las_size - EXTRA; // startpos of merged block
        linklist_remove(las_cat,q);
    }
    else if(las_alloc && !nxt_alloc){
        new_size = size + EXTRA + nxt_size;
        q = p;
        linklist_remove(nxt_cat,p + size + EXTRA);
    }
    else{
        new_size = las_size + EXTRA + size + EXTRA + nxt_size;
        q = p - las_size - EXTRA;
        linklist_remove(las_cat,q);
        linklist_remove(nxt_cat,p + size + EXTRA);
        // printf("%p %p %lu %lu %lu %lu\n",p,q,las_size,size,nxt_size,new_size);
    }

    new_cat = GET_CATEGORY(new_size);
    SETVAL(q,new_size | 0); // head
    SETVAL(q + new_size + HEADER,new_size | 0); // tail
    linklist_inserthead(new_cat,q);
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void){
    int i;
    for(i = 0;i < CATEGORY;i ++){
        unsigned char *p = mem_sbrk(SINGLEWORD);
        if((long)p < 0) return -1;
        SETVAL(p,0); // heads of linklists of different categories
    }

    if(!(CATEGORY & 1)){
        unsigned char *p = mem_sbrk(SINGLEWORD); // used for alignment
        if((long)p < 0) return -1;
    }

    unsigned char *p = mem_sbrk(EXTRA); // ADD HEADER : VIEW AS ALLOCATED SIZE=0 BLOCK
    if((long)p < 0) return -1;
    SETVAL(p,0 | 1); // head of HEADER
    SETVAL(p + SINGLEWORD,0);
    SETVAL(p + DOUBLEWORD,0);
    SETVAL(p + HEADER,0 | 1); // tail of HEADER

    p = mem_sbrk(SINGLEWORD); // ADD TAIL
    if((long)p < 0) return -1;
    SETVAL(p,0 | 1);
    // mm_checkheap(0);

    // HEADER AND TAIL are created to deal with merge_block
    return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size){
    size = (size + 15) & (~0xf); // align to 16
    // otherwise there may exist 8B pieces
    int cat;
    for(cat = 0;cat < CATEGORY;cat ++){
        if(CATEGORY_MINSIZE(cat) >= size + EXTRA) break;
    }
    if(cat == CATEGORY){
        // have to special judge for this
        assert(0);
    }

    int i,put = -1;
    for(i = cat;i < CATEGORY;i ++){
        if(GETVAL(LINKLIST_HEAD(i)) != 0){
            put = i;
            break;
        }
    } // find an available block with enough size
    
    unsigned char *p = NULL;

    // printf("%d %d %lu %u - ",cat,put,size,CATEGORY_MAXSIZE(put));

    if(put == -1){ // no available block, must extend heap
        p = extend_heap(size);
        if(p == NULL) return NULL; // malloc failed
        return p + HEADER;
    }

    p = ((unsigned char*)(mem_heap_lo()) + (size_t)(GETVAL(LINKLIST_HEAD(put)))); // get the head of linklist

    // printf("MALLOC %p %lu\n",p,size);

    place_block(p,size);
    // mm_checkheap(1);
    return p + HEADER;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr){

    // printf("FREE %p\n",ptr);

    if(ptr == NULL) return;
    size_t size = GET_SIZE(ptr - HEADER);
    int alloc_ = GET_ALLOC(ptr - HEADER);
    if(!alloc_) return;

    // printf("FREESIZE = %lu\n",size);

    SETVAL(ptr - HEADER,size | 0); // set head
    SETVAL(ptr + size,size | 0); // set tail
    // do not insert the block into linklist temporarily
    // deal with it in mergeblock
    merge_block(ptr - HEADER,size);
    // mm_checkheap(2);
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
    oldsize = GET_SIZE(oldptr - HEADER);
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
    printf("CHECKHEAP %d:\n",verbose);
    int i;
    for(i = 0;i < CATEGORY;i ++){
        printf("CATEGORY %d [%u,%u) : ",i,CATEGORY_MINSIZE(i),CATEGORY_MAXSIZE(i));
        unsigned char *p = LINKLIST_HEAD(i);
        if(GETVAL(p) != 0){
            p = GETP(GETVAL(p));
            size_t las_p = 0;
            while(1){
                size_t delta_nxt = GETVAL(p + DOUBLEWORD);
                size_t siz = GET_SIZE(p);
                int alloc = GET_ALLOC(p);
                printf("(%p,%lu,%d) ",p,siz + EXTRA,alloc);
                if(!(siz + EXTRA >= CATEGORY_MINSIZE(i) && siz + EXTRA <= CATEGORY_MAXSIZE(i))){
                    printf("CATEGORY %d [%u,%u) : ",i,CATEGORY_MINSIZE(i),CATEGORY_MAXSIZE(i));
                    printf("(%p,%lu,%d) ",p,siz + EXTRA,alloc);
                }
                assert(siz + EXTRA >= CATEGORY_MINSIZE(i) && siz + EXTRA <= CATEGORY_MAXSIZE(i));
                assert(!alloc);
                assert(GETVAL(p) == GETVAL(p + HEADER + siz));
                assert(GETVAL(p + SINGLEWORD) == las_p);
                if(delta_nxt == 0) break;
                las_p = DELTA(p);
                p = GETP(delta_nxt);
            }
        }
        printf("\n");
    }
    printf("\n");
    unsigned char * p;
    int flg = 0,las = 1;
    p = (unsigned char*)(mem_heap_lo()) + 4 * CATEGORY + (!(CATEGORY & 1)) * SINGLEWORD;
    while(p < (unsigned char*)(mem_heap_hi())){
        printf("%p,%u,%u ",p,GET_SIZE(p),GET_ALLOC(p));
        if(!las && !GET_ALLOC(p)){
            printf("ERROR NOTMERGED : %d\n",verbose);
            // assert(0);
            flg = 1;
        }
        if(GET_SIZE(p) > 0 && GETVAL(p) != GETVAL(p + GET_SIZE(p) + HEADER)){
            printf("ERROR HEADTAILNOTEQUAL : %d %u %u\n",verbose,GETVAL(p),GETVAL(p + GET_SIZE(p) + HEADER));
            // assert(0);
            flg = 1;
        }
        las = GET_ALLOC(p);
        p += (GET_SIZE(p) + EXTRA);
    }
    if(flg) assert(0);
    printf("\n");
}
