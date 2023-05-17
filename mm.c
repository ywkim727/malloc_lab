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

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "3 team",
    /* First member's full name */
    "YeongWoo Kim",
    /* First member's email address */
    "uddn@naver.com",
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

//가용리스트 조작을 위한 기본 상수와 매크로
#define WSIZE 8             //워드 크기
#define DSIZE 16            //더블 워드 크기
#define CHUNKSIZE (1<<12)   //초기 가용 블록과 힙 확장을 위한 기본 크기

#define MAX(x,y) ((x) > (y)? (x) : (y))         

#define PACK(size, alloc) ((size) | (alloc))            //크기와 할당 비트를 통합해서 헤더와 풋터에 저장 할 수 있는 값을 리턴

#define GET(p) (*(unsigned int *)(p))                   //인자p가 참조하는 워드를 읽어서 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val))      //인자p가 가리키는 워드에 val을 저장

#define GET_SIZE(p) (GET(p) & ~0x7)                     //주소 p에 있는 사이즈 리턴 (~0x7 : ...111000, &연산자 사용해 마지막 3비트를 제외한 값 추출)
#define GET_ALLOC(p) (GET(p) & 0x1)                     //할당 상태

#define HDRP(bp) ((char *)(bp) - WSIZE)                         //헤더를 가리키는 포인터를 리턴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)    //풋터를 가리티는 포인터를 리턴

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))     //다음 블록의 블록포인터를 리턴
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))     //이전 블록의 블록포인터를 리턴

static char *heap_listp;
static void *last_bp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {   //heap_listp의 시작 주소를 변경해줌
        return -1;
    }
    PUT(heap_listp, 0);                                     //시작 부분인 heap_listp에 0을 넣는다(가장 앞부분 4byte는 사용하지 않음)
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));            //header에 해당
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));            //footer에 해당
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));                //에필로그 블록 헤더
    heap_listp += (2*WSIZE);                                //heap_listp의 주소를 2*WSIZE만큼 옮겨준다

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {             //그 후 힙사이즈를 늘려준다, 인자 CHUNKSIZE/WSIZE = 2^10으로 넘겨줌
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;     //words를 짝수로 만들어줌, WSIZE 곱하면 size는 2^12 가 된다
    if ((long)(bp = mem_sbrk(size)) == -1) {                    //mem_sbrk(size)로 받아온 주소값을 bp에 할당 
        return NULL;
    }
    PUT(HDRP(bp), PACK(size, 0));                               //free블록의 헤더
    PUT(FTRP(bp), PACK(size, 0));                               //free블록의 풋터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));                       //새로운 에필로그 블록의 헤더

    return coalesce(bp);                                        //coalesce 과정을 진행한다
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));     //free블럭의 이전,다음 블럭 할당 정보를 받아온다(0,1)
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {                         //case1 : 이전,다음 모두 할당된 블럭일 경우
        last_bp = bp;
        return bp;                                          //coalesce 없이 bp를 반환
    }
    else if (prev_alloc && !next_alloc) {                   //case2 : 이전은 할당된 블럭, 다음은 free블럭일 경우  
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));              //size에 다음 블럭의 size를 더해준다 
        PUT(HDRP(bp), PACK(size, 0));                       //현재 블럭의 헤더와 다음 블럭의 풋터에 PACK(size,0) 값을 할당
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {                   //case3 : 이전은 free블럭, 다음은 할당된 블럭일 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));              //size에 이전 블럭의 size를 더해준다
        PUT(FTRP(bp), PACK(size, 0));                       //현재 블럭의 풋터와 이전 블럭의 헤더에 PACK(size,0) 값을 할당
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);                                 //bp는 이전 블럭으로 이동시킨다
    }
    else {                                                  //case4 : 이전, 다음 블럭 모두 free블럭일 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));  //size에 이전,다음 블럭의 size를 모두 더해준다
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));            //이전 블럭의 헤더와 다음 블럭의 풋터에 PACK(size,0) 값을 할당
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);                                 //bp는 이전 블럭으로 이동시킨다
    }
    last_bp = bp;
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) {                                             //size값에 따라 3가지 케이스로 asize를 할당한다
        return NULL;                                             //size = 0 이면 NULL (할당할 블럭이 없어서)
    }
    if (size <= DSIZE) {                                         //size <= DSIZE : asize = 2*DSIZE (Minimum block size = 2*DSIZE)
        asize = 2*DSIZE;
    }else {                                                      //size > DSIZE : DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE) (asize를 Double Word 단위로 정렬하기 위함)
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }
    if ((bp = find_fit(asize)) != NULL) {                        //find_fit을 호출하여 할당공간을 찾고 해당 주소를 bp에 넣어준다
        place(bp, asize);                                        //공간을 찾았으면 place를 호출하여 asize만큼 할당한다
        last_bp = bp;
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);                          //find_fit으로 공간을 찾지 못했다면 brk pointer를 증가시켜야 하므로 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {          //extendsize만큼 extend_heap 해준뒤 place 호출하여 asize만큼 할당한다
        return NULL;
    }
    place(bp, asize);
    last_bp = bp;
    return bp;
}

static void *find_fit(size_t asize) {                                           //next_fit 
    char *bp = last_bp;                                                         //bp에 last_bp를 넣어준다

    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {     //last_bp를 시작으로 공간의 사이즈가 0일때까지(마지막 도달) 탐색 
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {            //free공간이고 && asize를 충분히 넣을 수 있는 공간일 때
            last_bp = bp;                               
            return bp;                                                          //해당 bp를 리턴한다
        }
    }
                                                                                //위에서 찾지 못 했을 경우
    bp = heap_listp;                                                            //bp = 첫 시작인 heap_listp부터 시작해서
    while(bp < last_bp) {                                                       //최초의 last_bp까지 탐색을 시도한다
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp;
            return bp;
        }
    }
    return NULL;                                                                //모든 탐색을 시도해도 찾지 못 했다면 NULL을 리턴
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));                                          //csize는 현재 free블럭의 사이즈

    if((csize - asize) >= (2*DSIZE)) {                                          //case1: asize만큼 할당하고 남은 공간이 2DSIZE보다 크거나 같다면
        PUT(HDRP(bp), PACK(asize, 1));                                          //bp의 헤더와 풋터에 asize를
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);                                                     //남은 사이즈 csize-asize를 bp다음 블럭의 헤더,풋터에 넣어준다(가용블록의 분할)
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }else {                                                                     //case2 : 2*DSIZE보다 작다면
        PUT(HDRP(bp), PACK(csize, 1));                                          //남은 사이즈 csize-asize는 최소 블럭 사이즈보다 작으므로
        PUT(FTRP(bp), PACK(csize, 1));                                          //bp의 헤더와 풋터에 csize만큼 할당하면 나머지는 padding을 첨가하여 해결 가능하다
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));                                               //헤더와 풋터에 PACK(size,0)을 넣어줌으로써 free상태로 마킹한다
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);                                                               //그 후 coalesce를 시도하여 블럭을 합쳐준다
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);                                   //인자로 받아온 size만큼 malloc을 통해 새로 블럭을 만들어 newptr에 저장해준다
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);       //copysize는 인자 ptr로 받아온 기존 블럭의 사이즈
    if (size < copySize)                                        //ptr의 블럭 사이즈가 인자로 받아온 size보다 클 경우
      copySize = size;                                          //memcpy를 하는 과정에서 불필요한 메모리 공간을 침범하는 경우가 발생할 수 있으므로 copysize = size해줘야 한다
    memcpy(newptr, oldptr, copySize);                           //copysize만큼의 데이터를 oldptr에서 newptr로 복사한다
    mm_free(oldptr);                                            //기존의 블럭(ptr)을 free 시켜주고 newptr을 반환해준다
    return newptr;
}

