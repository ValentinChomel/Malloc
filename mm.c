// name: Hugo Tarle & Valentin Chomel
// id: hugo.tarle & valentin.chomel


//Final solution description :

/*  DESCRIPTION OF EMPTY BLOCK :
 *  --------------------------------------------
 *  |HEADER :   block size   |   |   |alloc bit|
 *  |------------------------------------------|
 *  | ptr to prev free block in same list      |
 *  |------------------------------------------|
 *  | ptr to next free block in same list      |
 *  |------------------------------------------|
 *  |FOOTER :   block size   |   |   |alloc bit|
 *  --------------------------------------------
 *
 *
 *  DESCRIPTION OF ALLOCATED BLOCK :
 *   --------------------------------------------
 *   |HEADER :   block size   |   |   |alloc bit|
 *   |------------------------------------------|
 *   |               Data                       |
 *   |------------------------------------------|
 *   |               Data                       |
 *   |------------------------------------------|
 *   |FOOTER :   block size   |   |   |alloc bit|
 *   --------------------------------------------
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "Tarle & Chomel",
    /* First member's full name */
    "Hugo Tarle",
    /* First member's email address */
    "hugo.tarle@polytechnique.edu",
    /* Second member's full name (leave blank if none) */
    "Valentin Chomel",
    /* Second member's email address (leave blank if none) */
    "valentin.chomel@polytechnique.edu"
};

/*Basic constants and macros */
#define WORD_SIZE 4  /*word and header/footer size (bytes) */
#define DOUBLE_SIZE 8  /*Double word size (bytes) */
#define CHUNKSIZE (1<<6) /*extend heap by this amount (bytes) */
#define OVERHEAD 24

#define SEG_LIST_COUNT  20     /*number of segregated lists*/

#define MAX(x,y) ((x) > (y) ? (x) : (y))

/*Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/*read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/*read the size, allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*Given bock ptr ptr, compute address of its header and footer */
#define HDRP(ptr)   ((char *)(ptr) - WORD_SIZE)
#define FTRP(ptr)   ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DOUBLE_SIZE)

/*Given block ptr ptr, compute address of next and previous blocks */
#define NEXT_BLKP(ptr)  ((char *)(ptr) + GET_SIZE(((char *)(ptr) - WORD_SIZE)))
#define PREV_BLKP(ptr)  ((char *)(ptr) - GET_SIZE(((char *)(ptr) - DOUBLE_SIZE)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*helper macros for seg list */
/*set the prev and next field of ptr to address nptr*/
#define PUT_PTR(p, ptr)  (*(unsigned int *)(p) = (unsigned int)(ptr))

/*get address of prev/next field of a free block in a seg_list with pointer ptr */
#define GET_PREV(ptr)       ((char *)ptr)
#define GET_NEXT(ptr)        ((char *)(ptr) + WORD_SIZE)

/*get address of the pre/next block in a seg_list (actual address) */
#define GET_PREV_BLK(ptr)   (*(char **)(ptr))
#define GET_NEXT_BLK(ptr)   (*(char **)(GET_NEXT(ptr)))

/*helper macro // seg-listst*/
#define SEG_LIST(ptr, index)  *((char **)ptr+index)

/*global variables */
static char *heap_listp = 0;
static void * seg_listp;       /*pointer pointing to start of seg_list (ptr to head of first list)*/

/* Function prototypes */    
static void *coalesce(void *ptr);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *place(void * ptr, size_t asize);
static void insert_free_block(void *ptr, size_t block_size);
static void remove_free_block(void *ptr);
//int mm_check(void);

/*
 * mm_init - Initialize the malloc package. The return value is -1 if there is a problem in performing  
 * the initialization, 0 otherwise. 
 */
int mm_init(void)
{
  int list_number; 
  seg_listp = mem_sbrk(SEG_LIST_COUNT*WORD_SIZE);
 
  /* initialize the seg_lists */
  for (list_number = 0; list_number < SEG_LIST_COUNT; list_number++) {
    SEG_LIST(seg_listp, list_number)= NULL;
  }

  /* create the initial empty heap */
  if ((heap_listp = mem_sbrk(4*WORD_SIZE))==(void *) -1)
	return -1; 
  PUT(heap_listp, 0);				/*Alignment padding */
  PUT(heap_listp + (1*WORD_SIZE), PACK(DOUBLE_SIZE, 1));  /*Prologue header */
  PUT(heap_listp + (2*WORD_SIZE), PACK(DOUBLE_SIZE, 1));  /*Prologue footer */
  PUT(heap_listp + (3*WORD_SIZE), PACK(0,1));       /* Epilogue header*/
  heap_listp += (2*WORD_SIZE);

  if (extend_heap(CHUNKSIZE/WORD_SIZE) == NULL)
  	return -1;
  return 0;
}

/*
 * extend_heap: extends the heap with free block
 */ 
static void *extend_heap(size_t words)
{
  char *ptr4;
  size_t size;

  /*Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1)*WORD_SIZE : words * WORD_SIZE;
  if ((long)(ptr4 = mem_sbrk(size)) == -1)
  	return NULL;

  /*initialize free block header/footer and the epilogue header*/
  PUT(HDRP(ptr4), PACK(size, 0));   	   /*Free Block header*/
  PUT(FTRP(ptr4), PACK(size, 0));   	   /*Free Block footer*/
  PUT(HDRP(NEXT_BLKP(ptr4)), PACK(0, 1));  /*New Epilogue header*/
  insert_free_block(ptr4, size); 

  /*coalesce if the previous block was free */
  return coalesce(ptr4);
}

/* PREVIOUS VERSION :

//extension_heap extends the heap with free block
static void* extension_heap(size_t words){
    char *ptr;
    size_t size;
    size = (words % 2) ? (words + 1) * SINGLEWORD : words * SINGLEWORD;    //even number
    if(size < OVERHEAD){
        size = OVERHEAD;
    }
    if((long)(ptr = mem_sbrk(size)) == -1){                                                  
        return NULL;
    }
    PUT(HDRP(ptr), PACK(size, 0));                                                           
    PUT(FTRP(ptr), PACK(size, 0));                                                           
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));                                                   
    return coalesce(ptr);
}

*/

/*
 * find_fit -return a ptr to a free block that can accommodate asize
 * implemented with best-fit strategy, scanning through the list for
 * the smallest block that can fit asize 
 * --helped--
 */
static void *find_fit(size_t asize)
{   
    size_t size = asize;
    int list_number = 0;
    void *list_ptr = NULL;
 
    while (list_number < SEG_LIST_COUNT) {
	
     if ((list_number == SEG_LIST_COUNT - 1) || ((size <= 1) && (SEG_LIST(seg_listp, list_number)!= NULL))) {
       list_ptr  = SEG_LIST(seg_listp, list_number);

        // locate the smallest block that can fit :
	while ((list_ptr != NULL) && (asize > GET_SIZE(HDRP(list_ptr)))){
          list_ptr = GET_PREV_BLK(list_ptr);
        }
        if (list_ptr != NULL) {
         break;
        }
      }
      list_number++;
      size = size >> 1;
    }
    return list_ptr;  
}

/*
 * place - occupy asize of block pointed by ptr, coalesce the remaining free
 * space if the block size is larger than allocated size.
 */
static void *place(void *ptr, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(ptr));
    void *np = NULL;
    remove_free_block(ptr);
    
    /* if the remaining free space is larger than min-block-size --> coalesce*/
    if ((csize - asize) >= (2*DOUBLE_SIZE)) {
      if ((csize - asize) >= 200){
        PUT(HDRP(ptr), PACK(csize - asize, 0));
        PUT(FTRP(ptr), PACK(csize - asize, 0));
        np = NEXT_BLKP(ptr);
        PUT(HDRP(np), PACK(asize, 1));
        PUT(FTRP(np), PACK(asize, 1));
        insert_free_block(ptr, csize - asize);
        return np;  
      }
      else {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        np = NEXT_BLKP(ptr);
        PUT(HDRP(np), PACK(csize - asize, 0));
        PUT(FTRP(np), PACK(csize - asize, 0));
        insert_free_block(np, csize - asize);
      }
    }
    else {
       PUT(HDRP(ptr), PACK(csize, 1));
       PUT(FTRP(ptr), PACK(csize, 1));
    }
    return ptr;
}

/* PREVIOUS VERSION :

static void place(void *ptr, size_t size2){
    size_t size_p = GET_SIZE(HDRP(ptr));
    if((size_p - size2) >= OVERHEAD){
        PUT(HDRP(ptr), PACK(size2, 1));
        PUT(FTRP(ptr), PACK(size2, 1));
        remove_block(ptr);
        ptr = NEXT_BLKP(ptr);
        PUT(HDRP(ptr), PACK(size_p - size2, 0));
        PUT(FTRP(ptr), PACK(size_p - size2, 0));
        coalesce(ptr);
    }
    else {
        PUT(HDRP(ptr), PACK(size_p, 1));
        PUT(FTRP(ptr), PACK(size_p, 1));
        remove_block(ptr);
    }
}


*/

/* 
 * mm_malloc- malloc block by finding a block that fits (call find_fit),
 * if no fit, extend the heap for more space, then call place to place
 * the block. 
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;  /*adjusted block size */
    size_t extendsize; /*amount ot extend heap if no fit */
    char *ptr3;
    char *ptr;

    /*ignore spurious requests */
    if (size == 0)
      return NULL;
    
    /*adjusted block size to include overhead and alignment reqs*/
    if (size <= DOUBLE_SIZE)
      asize = 2*DOUBLE_SIZE;
    else
      asize = DOUBLE_SIZE * ((size + (DOUBLE_SIZE) + (DOUBLE_SIZE - 1)) / DOUBLE_SIZE);

    /* Search the free list for a fit */
    if ((ptr3 = find_fit(asize)) != NULL) {
      ptr =  place(ptr3, asize);
      return ptr;
    }
    
    /*no fit found, get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((ptr3 = extend_heap(extendsize/WORD_SIZE)) == NULL)
      return NULL;
    ptr =  place(ptr3, asize);
    return ptr;
}

/* PREVIOUS VERSION :

//MY DESCRIPTION: First, allocate the memory to the first place with have correct size. If it's not possible, split the block.
void *mm_malloc(size_t size)
{
    size_t size2;    //adjusted block
    size_t size3;    //extended
    char *ptr;
    if(size <= 0){    //ignore
        return NULL;
    }
    size2 = (ALIGN(size) + ALIGNMENT>OVERHEAD?ALIGN(size) + ALIGNMENT:OVERHEAD);
    if((ptr = find_free(size2))){
        place(ptr, size2);
        return ptr;
    }
    size3 = (size2>CHUNKSIZE?size2:CHUNKSIZE);
    if((ptr = extension_heap(size3/WORD_SIZE)) == NULL){
        return NULL;    //unable to extend heap space
    }
    place(ptr, size2);   //newly extended space
    return ptr;
}

*/

/*
 * mm_free - Freeing a block by update allocation bit, and insert 
 * into the seg_list for reuse. Coalesce if possible.
 */
void mm_free(void *ptr)
{
    if(!ptr){
        return;
    }
    size_t size = GET_SIZE(HDRP(ptr));
    
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    insert_free_block(ptr, size);
    coalesce(ptr);
}

/*
 * coalesce - check four cases and try to merge the freed block at *ptr with previous and next block
 */
static void *coalesce(void *ptr)
{
  size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
  size_t size = GET_SIZE(HDRP(ptr));
  /*case 1 : both prev and next block are allocated --> no coalesce*/ 
  if (prev_alloc && next_alloc) {		
    return ptr;
  } 
  /*case 2 : prev block allocated, next not --> coalesce with next*/
  else if (prev_alloc && !next_alloc) {	
    remove_free_block(ptr);
    remove_free_block(NEXT_BLKP(ptr));
    size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
  }
  /*case 3 : prev block free, next allocated --> coalesce with prev*/
  else if (!prev_alloc && next_alloc) { 	
    remove_free_block(ptr);
    remove_free_block(PREV_BLKP(ptr));
    size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
    ptr = PREV_BLKP(ptr);
  }
  /*case 4 : both prev and next free --> coalsce three blocks into one*/
  else {					
    remove_free_block(PREV_BLKP(ptr));
    remove_free_block(ptr);
    remove_free_block(NEXT_BLKP(ptr));
    size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(FTRP(NEXT_BLKP(ptr)));
    PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
    ptr = PREV_BLKP(ptr);
  }

  /*put coalesced block into the seg_list for re-use*/
  insert_free_block(ptr, size);
  return ptr;
}

 
/*
 * mm_realloc - implementaed with optimzation on every case:
 * Check if: ptr = null or size = 0 or oldptr size = new size
 * If none, 3 cases:
 * Case 1: If new size requested < size of oldptr
 *         We can shrink the size of oldptr, update header footer,
 *         and free & coalesce the remaining free space 
 * If larger size, case 2 & 3.
 * Case 2: Check if next block in memory after ptr is free
 * 	   and can fit the new size, and if yes, combine the two
 * Case 3: call mm_malloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    void * nextptr;
    size_t copySize, asize, nsize;
   
    /*if size = 0, we want to free ptr*/
    if (size == 0) {
      mm_free(oldptr);
      return NULL;
    }   

    /*if oldptr is null, we want to call malloc(size) */
    if (oldptr == NULL) {
      return mm_malloc(size);
    }
    asize = ALIGN(size);

    /*realloc ptr with size*/
   copySize =GET_SIZE(HDRP(oldptr))-DOUBLE_SIZE;
  
    if (asize == copySize) {
      return oldptr;
    }

    /*Case 1: */
    if (asize < copySize) {
      /*if remaining space isn't enough to store, return oldptr*/
      if (copySize - asize - DOUBLE_SIZE <= DOUBLE_SIZE)
	return oldptr;
      PUT(HDRP(oldptr), PACK(asize + DOUBLE_SIZE, 1));
      PUT(FTRP(oldptr), PACK(asize + DOUBLE_SIZE, 1));
      newptr = oldptr;
      oldptr = NEXT_BLKP(newptr);
      /*free*/
      PUT(HDRP(oldptr), PACK(copySize - asize, 0));
      PUT(FTRP(oldptr), PACK(copySize - asize, 0));
      insert_free_block(oldptr, GET_SIZE(HDRP(oldptr)));
      coalesce(oldptr);
      return newptr; 
    }

    /*Case 2: */
    nextptr = NEXT_BLKP(oldptr);
    /*Check if the next block after oldptr block is free*/
    if (nextptr != NULL && !GET_ALLOC(HDRP(nextptr))) {
       nsize = GET_SIZE(HDRP(nextptr));	
      if (nsize + copySize >= asize) {
	remove_free_block(nextptr);
	if (nsize + copySize - asize <= DOUBLE_SIZE) {
  	  //if remaining space in next block can't hold values, use it all
  	  PUT(HDRP(oldptr), PACK(copySize + DOUBLE_SIZE + nsize, 1));
          PUT(FTRP(oldptr), PACK(copySize + DOUBLE_SIZE + nsize, 1));
          return oldptr;
	}
 	else{   
          PUT(HDRP(oldptr), PACK(asize + DOUBLE_SIZE, 1));
          PUT(FTRP(oldptr), PACK(asize + DOUBLE_SIZE, 1));
	  newptr = oldptr;
	  oldptr = NEXT_BLKP(newptr);
	  PUT(HDRP(oldptr), PACK(copySize + nsize - asize, 0));
      	  PUT(FTRP(oldptr), PACK(copySize + nsize - asize, 0));
      	  insert_free_block(oldptr, GET_SIZE(HDRP(oldptr)));
      	  coalesce(oldptr);
      	  return newptr;
	}
      } 
    }

    /*Case 3: */
    newptr = mm_malloc(size); 
    if (newptr == NULL)
      return NULL;
    /*copy over the data from oldptr*/
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/* PREVIOUS VERSION :

//MY DESCRIPTION: There is 3 actions, it depends of the the size of the new block: smaller, equal or greater.
void *mm_realloc(void *ptr, size_t size)
{
    size_t copySize;    //old size of the block
    void *newptr;    //new block pointer
    size_t size2 = (ALIGN(size) + ALIGNMENT>OVERHEAD?ALIGN(size) + ALIGNMENT:OVERHEAD);    //adjusted size
    if(size <= 0){
        mm_free(ptr);
        return 0;
    }
    if(ptr == NULL){
        return mm_malloc(size);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if(copySize == size2){
        return ptr;
    }
    if(size2 <= copySize){
        size = size2;
        if(copySize - size <= OVERHEAD){
            return ptr;    //old block pointer
        }
        PUT(HDRP(ptr), PACK(size, 1));    //update the size in the header of the reallocated block
        PUT(FTRP(ptr), PACK(size, 1));    //update the size in the footer of the reallocated block
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(copySize - size, 1));    //update the size in the header of the next block
        mm_free(NEXT_BLKP(ptr));
        return ptr;
    }
    newptr = mm_malloc(size);
    if(!newptr){
        return 0;
    }
    if(size < copySize){
        copySize = size;
    }
    memcpy(newptr, ptr, copySize);    //old data -> new block
    mm_free(ptr);    //unallocate the old block
    return newptr;
}

*/


/*
 * insert_free_block - takes a pointer to a block ptr and add it to the seg list
 * each individual list of the same size class is sorted by actual block size
 */
static void insert_free_block(void *ptr, size_t block_size)
{
  void *list_ptr = NULL;
  void *insert_loc = NULL;
  /*find the list number / index for this block*/
  int list_number = 0; 
  while ((list_number < (SEG_LIST_COUNT - 1)) && (block_size > 1)) {
    block_size = block_size >> 1;
    list_number++;
  }

  list_ptr = SEG_LIST(seg_listp, list_number);
  /*find the location to insert, so that the list  will be sorted by block size*/
  while ((list_ptr != NULL) && (block_size > GET_SIZE(HDRP(list_ptr)))) {
    insert_loc = list_ptr;
    list_ptr = GET_PREV_BLK(list_ptr);
  }
   
  /*insert the free block based on the condition of insert_loc and list_ptr*/
  if (list_ptr) {
    if (insert_loc) {  //between insert_loc and list_ptr
       PUT_PTR(GET_PREV(insert_loc), ptr);
       PUT_PTR(GET_NEXT(ptr), insert_loc);
       PUT_PTR(GET_PREV(ptr), list_ptr);
       PUT_PTR(GET_NEXT(list_ptr), ptr); 
    }
    else {    //if ptr smaller than first item in list_ptr, insert at the beginning
       PUT_PTR(GET_NEXT(list_ptr), ptr);
       PUT_PTR(GET_PREV(ptr), list_ptr);
       PUT_PTR(GET_NEXT(ptr), NULL);
       SEG_LIST(seg_listp, list_number)=ptr;
    }
  }
  else {     
    if (insert_loc) {
      PUT_PTR(GET_NEXT(ptr), insert_loc);
      PUT_PTR(GET_PREV(insert_loc), ptr);
      PUT_PTR(GET_PREV(ptr), NULL);    
    }
    else {
      SEG_LIST(seg_listp, list_number)= ptr;
      PUT_PTR(GET_PREV(ptr), NULL);
      PUT_PTR(GET_NEXT(ptr), NULL);
      return;
    }
  }
  return; 
}

/*
 * remove_free_block- remove a free block ptr from seg_list
 * update prev/next pointers 
 */
static void remove_free_block(void *ptr)
{ 
  int list_number = 0; 
  size_t block_size = GET_SIZE(HDRP(ptr));
  
  /*if ptr is the head of a seg_list :*/
  if (GET_NEXT_BLK(ptr) == NULL) {
  // find the list number / index for this block
    while (list_number < (SEG_LIST_COUNT - 1) && block_size > 1) {
      block_size = block_size >> 1;
      list_number++;
    }
    SEG_LIST(seg_listp, list_number)= GET_PREV_BLK(ptr);
    if (SEG_LIST(seg_listp, list_number) != NULL) {
      PUT_PTR(GET_NEXT(SEG_LIST(seg_listp, list_number)), NULL);
    }
    return;
  }
  
  /*if ptr is not the head of a seg_list, update the
   next pointer of prev block and prev pointer of next block*/
  PUT_PTR(GET_PREV(GET_NEXT_BLK(ptr)), GET_PREV_BLK(ptr)); 
  if (GET_PREV_BLK(ptr) != NULL) {
    PUT_PTR(GET_NEXT(GET_PREV_BLK(ptr)), GET_NEXT_BLK(ptr));
  } 
}

/* PREVIOUS VERSION :

static void remove_block(void *ptr){
    if(PREV_FREEP(ptr)){
        NEXT_FREEP(PREV_FREEP(ptr)) = NEXT_FREEP(ptr);
    }
    else{
        free_listp = NEXT_FREEP(ptr);
    }
    PREV_FREEP(NEXT_FREEP(ptr)) = PREV_FREEP(ptr);
}

*/

/*
 * mm_check
 */
/*int mm_check(void){
    void *ptr = heap_listp;
    if((GET_SIZE(HDRP(heap_listp)) != OVERHEAD) || !GET_ALLOC(HDRP(heap_listp))){
         printf("Error: Bad prologue header\n");
         return 0;
    }
    int a=0;
    if(NEXT_FREEP(ptr) < mem_heap_lo() || NEXT_FREEP(ptr) > mem_heap_hi()){
        a=-1;
        printf("Error: Out of bounds\n");
    }
    if(PREV_FREEP(ptr) < mem_heap_lo() || PREV_FREEP(ptr) > mem_heap_hi()){
        a=-1;
        printf("Error: Out of bounds\n");
    }
    if((size_t)ptr % 8){
        a=-1;
        printf("Error: Not aligned\n");
    }
    if(GET(HDRP(ptr)) != GET(FTRP(ptr))){
        a=-1;
        printf("Error: Problem header and footer\n");
    }
    if(a == -1){
        printf("Error: Inconsistency\n");
        return 0;
    }
    for(ptr = free_listp; GET_ALLOC(HDRP(ptr)) == 0; ptr = NEXT_FREEP(ptr)){
            a=0;
	    if(NEXT_FREEP(ptr) < mem_heap_lo() || NEXT_FREEP(ptr) > mem_heap_hi()){
		a=-1;
                printf("Error: Out of bounds\n");
	    }
	    if(PREV_FREEP(ptr) < mem_heap_lo() || PREV_FREEP(ptr) > mem_heap_hi()){
		a=-1;
                printf("Error: Out of bounds\n");
	    }
	    if((size_t)ptr % 8){
		a=-1;
                printf("Error: Not aligned\n");
	    }
	    if(GET(HDRP(ptr)) != GET(FTRP(ptr))){
		a=-1;
                printf("Error: Problem header and footer\n");
	    }
         if(a == -1){
             printf("Error: Inconsistency\n");
             return 0;
         }
    }
    printf("No inconsistency\n");
    return 1;
}*/

