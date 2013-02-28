/* -*- Mode: C++; c-basic-offset: 4; indent-tabs-mode: nil -*- */
#include <stdio.h>
#include <sys/mman.h>
#include <string.h>
//#include <malloc.h>
#include <stdlib.h>
#include <stdint.h>
#include <fcntl.h>
#include <smmintrin.h>

//#define D_XOR
#define D_CRC

#ifdef DEBUG
#define ASSERT(x) \
    do { \
        if (!(x)) { \
            fprintf(stderr, "ASSERT failed at line %d in file %s\n", __LINE__, __FILE__); \
        } \
    } while (0)
#else
#define ASSERT(x)
#endif

#define PTR_TO_OFFSET(p) (((char*) (p)) - start_address)
#define OFFSET_TO_PTR(o) (start_address + (o))
#define OFFSET_TO_HDF(o) ((header_free*) (start_address + (o)))
#define OFFSET_TO_HDR(o) ((header*) (start_address + (o)))
#define OFFSET_TO_PTR(o) (start_address + (o))

#define PAGE_SIZE 0x1000
#define CACHE_LINE_SIZE 64
#define NEW_ALLOC_PAGES 1024
#define NIL 0xFFFFFFFFFFFFFFFF
#define BASE_SIZE 64
#define BASE_SIZE_MASK  (BASE_SIZE - 1)
#define NR_SIZES (4 * 1024/ BASE_SIZE)


static char* start_address;
static char* free_zone;
static char* end_address;
static unsigned nr_pages;

typedef struct header {
    int64_t size;
} header;

typedef struct header_free {
    int64_t size;
    uint64_t next;
    uint64_t prev;
} header_free;

typedef struct header_dna {
    header_free header;
    unsigned long time_added;
} header_dna;

typedef struct list_head {
    uint64_t position;
    struct list_head* next;
} list_head;

static unsigned char* bitmap;
static unsigned long bitmap_size;
static list_head* free_lists[NR_SIZES + 1];
static list_head* free_list_ends[NR_SIZES + 1];
static uint64_t dont_allocate_list_head;
static uint64_t dont_allocate_list_tail;
static unsigned long dont_allocate_wait;

static inline unsigned long rdtsc_()
{
    unsigned hi, lo;
    __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
    return ( (unsigned long)lo)|( ((unsigned long)hi)<<32 );
}

static inline void clflush(volatile char* __p)
{
    return;
    asm volatile("clflush %0" : "+m" (__p));
}

static inline void mfence()
{
    return;
    asm volatile("mfence":::"memory");
}

static inline void flushRange(char* start, char* end)
{
    char* ptr;
    return;
    for (ptr = start; ptr < end + CACHE_LINE_SIZE; ptr += CACHE_LINE_SIZE) {
        clflush(ptr);
    }
}

static inline int64_t xorCompute(char* location, uint32_t size)
{
    uint64_t offset = location - start_address;
    uint64_t chk = (offset ^ size) & 0x00FFFFFFFFFFFFFF;
    uint64_t chk_next = chk << 8;
    int i;
    for (i = 0; i < 6; i++) {
        chk ^= (chk_next & 0x00FF000000000000);
        chk_next = chk_next << 8;
    }
    return size | (chk & 0x00FF000000000000);
}

static inline uint32_t xorGetSize(int64_t hsize)
{
    return (uint32_t) (hsize & 0xFF00FFFFFFFFFFFF);
}

static inline int64_t crcCompute(char* location, uint32_t size)
{
    uint32_t offset = location - start_address;
    uint64_t chk = _mm_crc32_u32(offset, size);
    chk = chk << 32;
    return size | (chk & 0x00FF000000000000);
}

static inline uint32_t crcGetSize(int64_t hsize)
{
    return (uint32_t) (hsize & 0xFF00FFFFFFFFFFFF);
}

/* Return the index of the size that best fits an object of size size.
 */
static inline int getBestFit(uint32_t size)
{
    int index;
    if (size > NR_SIZES * BASE_SIZE) {
        return NR_SIZES;
    }
    index = size / BASE_SIZE - 1;
    if (size & BASE_SIZE_MASK) {
        index++;
    }
    return index;
}

static inline uint32_t isFreeForward(uint64_t location)
{
    uint32_t n = 0;
    unsigned index = (location / BASE_SIZE) >> 3;
    uint64_t end = free_zone - start_address;
    unsigned mask = 1 << ((location / BASE_SIZE) & 0x00000007);

    while (location < end && !(bitmap[index] & mask)) {
        n++;
        location += BASE_SIZE;
        if (mask == 128) {
            mask = 1;
            index++;
        } else {
            mask = mask << 1;
        }
    }

    return n;
}

static inline uint32_t isFreeBackward(uint64_t location)
{
    uint32_t n = 0;
    int32_t index = (location / BASE_SIZE) >> 3;
    unsigned mask = 1 << ((location / BASE_SIZE) & 0x00000007);

    if (start_address + location > free_zone)
        return 0;

    if (mask == 1) {
        if (index == 0) {
            return 0;
        }
        mask = 128;
        index--;
    } else {
        mask = mask >> 1;
    }

    while (index >= 0 && !(bitmap[index] & mask)) {
        n++;
        if (mask == 1) {
            if (index == 0) {
                return n;
            }
            mask = 128;
            index--;
        } else {
            mask = mask >> 1;
        }
    }
    return n;
}

static inline void makeOne(uint64_t location, uint32_t size) {
    unsigned index = (location / BASE_SIZE) >> 3;
    unsigned mask = 1 << ((location / BASE_SIZE) & 0x00000007);
    uint32_t i;

    for (i = 0; i < size; i++) {
        bitmap[index] = bitmap[index] | mask;
        if (mask == 128) {
            mask = 1;
            index++;
        } else {
            mask = mask << 1;
        }
    }
}

static inline void makeZero(uint64_t location, uint32_t size) {
    unsigned index = (location / BASE_SIZE) >> 3;
    unsigned mask = 1 << ((location / BASE_SIZE) & 0x00000007);
    uint32_t i;

    for (i = 0; i < size; i++) {
        bitmap[index] = bitmap[index] & ~mask;
        if (mask == 128) {
            mask = 1;
            index++;
        } else {
            mask = mask << 1;
        }
    }
}

/* Get more memory from the OS. The size of the newly allocated memory has to be
 * at least size bytes. The default is 4 KB.
 */
static inline int getMoreMemory(uint32_t size)
{
    uint32_t newPages = NEW_ALLOC_PAGES;
    char* addr;
    unsigned long new_bitmap_size, i;

    while (size > newPages * PAGE_SIZE) {
        newPages++;
    }

#ifdef _GNU_SOURCE
    addr = (char*) mremap(start_address, nr_pages * PAGE_SIZE,
                          (newPages + nr_pages) * PAGE_SIZE, MREMAP_MAYMOVE);
#else
    addr = (char*) mmap(end_address, newPages * PAGE_SIZE, PROT_READ | PROT_WRITE,
                        MAP_ANON | MAP_PRIVATE | MAP_FIXED, 0, 0);
#endif

    if (addr == MAP_FAILED) {
        perror("mremap failed");
        return -1;
    }

#ifdef _GNU_SOURCE
    if (addr != start_address) {
        end_address = end_address + newPages * PAGE_SIZE - start_address + addr;
        free_zone = free_zone - start_address + addr;
        start_address = addr;
    } else {
        end_address += newPages * PAGE_SIZE;
    }
#else
    end_address += newPages * PAGE_SIZE;
#endif

    nr_pages += newPages;

    new_bitmap_size = bitmap_size + newPages * PAGE_SIZE / BASE_SIZE / 8;

    bitmap = (unsigned char*) realloc(bitmap, new_bitmap_size);

    for (i = bitmap_size; i < new_bitmap_size; i++) {
        bitmap[i] = 0;
    }

    bitmap_size = new_bitmap_size;

    return 0;
}


/* Given a size, the function returns a pointer to a free region of that size. The region's actual
 * size (rounded to a multiple of BASE_SIZE) is returned in the actualSize argument.
 */
static char* getFreeLocation(uint32_t size, uint32_t* actSize)
{
    int index = getBestFit(size);
    uint32_t actualSize;
    char* freeLocation = NULL;

    if (index < NR_SIZES) {
        actualSize = (index + 1) * BASE_SIZE;
    } else {
        if (size & BASE_SIZE_MASK) {
            actualSize = (size & ~BASE_SIZE_MASK) + BASE_SIZE;
        } else {
            actualSize = size;
        }
    }
    *actSize = actualSize;


    while (!freeLocation && index <= NR_SIZES) {
        if (!free_lists[index]) {
            index++;
            //break;
            continue;
        }

        uint64_t location = 0;
        uint32_t free_space = 0;

        do {
            list_head* tmp = free_lists[index];
            uint32_t back_space;
            location = free_lists[index]->position;
            free_lists[index] = free_lists[index]->next;
            free(tmp);
            if (free_lists[index] == NULL)
                free_list_ends[index] = NULL;
            free_space = isFreeForward(location) * BASE_SIZE;
            back_space = isFreeBackward(location);
            free_space += back_space * BASE_SIZE;
            location -= back_space * BASE_SIZE;
        } while (free_space < actualSize && free_lists[index]);

        if (free_space >= actualSize) {
            uint32_t n = free_space;
            char* ptr = start_address + location;
            unsigned char exactFit = 0;
            while (n > 0) {
                header* hd = (header*)ptr;
                uint32_t crt_size;

                //test that the bitmap is correct
                if (hd->size >= 0) {
                    fprintf(stderr, "Bitmap corruption detected\n");
                }
#ifdef D_XOR
                crt_size = xorGetSize(-hd->size);
                if (xorCompute(ptr, crt_size) != -hd->size) {
                    fprintf(stderr, "Header corruption detected!\n");
                    exit(-1);
                }
#else
#ifdef D_CRC
                crt_size = crcGetSize(-hd->size);
                if (crcCompute(ptr, crt_size) != -hd->size) {
                    fprintf(stderr, "Header corruption detected!\n");
                    exit(-1);
                }
#else
                crt_size = -hd->size;
#endif
#endif
                n -= crt_size;
                ptr += crt_size;
                if (free_space - n == actualSize) {
                    exactFit = 1;
                }
            }
            if (free_space > actualSize) {
                list_head* lh;

                if (!exactFit) {
                    //must write a new header
                    header* hd = (header*) (start_address + location + actualSize);
#ifdef D_XOR
                    hd->size = -xorCompute(start_address + location + actualSize, free_space - actualSize);
#else
#ifdef D_CRC
                    hd->size = -crcCompute(start_address + location + actualSize, free_space - actualSize);
#else
                    hd->size = -(uint64_t)(free_space - actualSize);
#endif
#endif
                }

                lh = (list_head*)malloc(sizeof(list_head));
                lh->position = location + actualSize;
                lh->next = NULL;
                index = getBestFit(free_space - actualSize);
                if (free_list_ends[index])
                    free_list_ends[index]->next = lh;
                free_list_ends[index] = lh;
                if (!free_lists[index])
                    free_lists[index] = lh;
            }
            freeLocation = start_address + location;
            break;
        }
    }


    if (!freeLocation) {
        if (free_zone + actualSize > end_address) {
            if (getMoreMemory(actualSize) < 0) {
                return NULL;
            }
        }
        freeLocation = free_zone;
        free_zone += actualSize;
    }

    makeOne((uint64_t)(freeLocation - start_address), actualSize / BASE_SIZE);

    return freeLocation;
}

/* Insert the free location in the appropriate free list.
 */
static inline void insertFreeLocation(char* location, uint32_t sizeForward, uint32_t totalSize)
{
    header* nh;
    list_head* lh;
    int index;

    ASSERT(!(totalSize & BASE_SIZE_MASK));

    if (location + sizeForward >= free_zone && location < free_zone) {
        // merge with the free zone
        free_zone = location + sizeForward - totalSize;
        ((header*) location)->size = 0;
        mfence();
        clflush(location);
        return;
    }

    nh = (header*) location;
#ifdef D_XOR
    nh->size = -xorCompute(location, sizeForward);
#else
#ifdef D_CRC
    nh->size = -crcCompute(location, sizeForward);
#else
    nh->size = -(int32_t)sizeForward;
#endif
#endif

    // flush the header containing the new size to memory -- marks an unrevertible delete
    mfence();
    clflush((char*) nh);
    mfence();

    // put hint in free lists
    lh = (list_head*)malloc(sizeof(list_head));
    index = getBestFit(totalSize);
    lh->position = (uint64_t)((location - start_address) + sizeForward - totalSize);
    lh->next = NULL;
    if (free_list_ends[index])
        free_list_ends[index]->next = lh;
    free_list_ends[index] = lh;
    if (!free_lists[index])
        free_lists[index] = lh;

    if (sizeForward != totalSize) {
        lh = (list_head*)malloc(sizeof(list_head));
        index = getBestFit(sizeForward);
        lh->position = (uint64_t)(location - start_address);
        lh->next = NULL;
        if (free_list_ends[index])
            free_list_ends[index]->next = lh;
        free_list_ends[index] = lh;
        if (!free_lists[index])
            free_lists[index] = lh;
    }
}

/* Try to extend the given free location with neighboring free locations.
 */
static inline uint32_t extendFreeLocation(char* location, uint32_t* size)
{
    uint32_t n;
    uint64_t offset = (uint64_t)(location - start_address);

    makeZero(offset, *size / BASE_SIZE);

    n = isFreeForward(offset);

    *size = n * BASE_SIZE;
    n = isFreeBackward(offset);
    //location = location - n * BASE_SIZE;
    return *size + n * BASE_SIZE;
}

/* Add location to the don't allocate list.
 */
static inline void putInDNAList(char* location, uint32_t size)
{
    header_dna* hdna = (header_dna*) location;
    //footer* ft = (footer*) (location + size - sizeof(footer));

#ifdef D_XOR
    if (hdna->header.size != xorCompute(location, size)) {
        fprintf(stderr, "Allocated region header corruption detected!\n");
    }
    hdna->header.size = -xorCompute(location, size + 1);
#else
#ifdef D_CRC
    if (hdna->header.size != crcCompute(location, size)) {
        fprintf(stderr, "Allocated region header corruption detected!\n");
    }
    hdna->header.size = -crcCompute(location, size + 1);

#else
    hdna->header.size = -(size + 1);
#endif
#endif

    hdna->time_added = rdtsc_();

    mfence();
    clflush(location);
    mfence();

    //ft->size = -(size + 1);

    if (dont_allocate_list_tail == NIL) {
        dont_allocate_list_head = dont_allocate_list_tail = PTR_TO_OFFSET(location);
    } else {
        header_dna* hdna_tail = (header_dna*) OFFSET_TO_PTR(dont_allocate_list_tail);
        hdna_tail->header.next = PTR_TO_OFFSET(location);
        dont_allocate_list_tail = PTR_TO_OFFSET(location);
    }
}

/* Increments the operations counter and checks if there is a location that can be
 * taken out of the don't allocate list.
 */
static void incrementTime()
{
    char* location;
    header_dna* hdna;

    if (dont_allocate_list_head == NIL) {
        return;
    }
    location = OFFSET_TO_PTR(dont_allocate_list_head);
    hdna = (header_dna*) location;
    if (rdtsc_() >= hdna->time_added + dont_allocate_wait) {
        char* location;
        uint32_t size, totalSize;

        // remove from don't allocate list and put in free list
        if (dont_allocate_list_head == dont_allocate_list_tail) {
            dont_allocate_list_head = dont_allocate_list_tail = NIL;
        } else {
            dont_allocate_list_head = hdna->header.next;
        }
        location = (char*) hdna;
#ifdef D_XOR
        size = xorGetSize(-hdna->header.size);
        if (hdna->header.size != -xorCompute(location, size)) {
            cerr << "Checksum error!" << endl;
        }
        size = size - 1;
#else
#ifdef D_CRC
        size = crcGetSize(-hdna->header.size);
        if (hdna->header.size != -crcCompute(location, size)) {
            fprintf(stderr, "NVMalloc checksum error!\n");
        }
        size = size - 1;
#else
        size = (uint32_t) (-hdna->header.size - 1);
#endif
#endif
        totalSize = extendFreeLocation(location, &size);
        insertFreeLocation(location, size, totalSize);
    }
}

/* Initialization function
 */
void nvmalloc_init(unsigned nrPages, unsigned long freeWait)
{
    int i;
#ifdef _GNU_SOURCE_
    start_address = (char*) mmap(NULL, nrPages * PAGE_SIZE, PROT_READ | PROT_WRITE,
                                 MAP_ANONYMOUS | MAP_PRIVATE, 0, 0);
#else
    start_address = (char*) mmap(NULL, nrPages * PAGE_SIZE, PROT_READ | PROT_WRITE,
                                 MAP_ANON | MAP_PRIVATE, 0, 0);
#endif
    if ((void*) start_address == MAP_FAILED) {
        perror("MAP FAILED");
    }
    nr_pages = nrPages;
    free_zone = start_address;
    end_address = start_address + nrPages * PAGE_SIZE;

    dont_allocate_list_head = NIL;
    dont_allocate_list_tail = NIL;
    dont_allocate_wait = freeWait;

    bitmap = (unsigned char*) calloc(nrPages * PAGE_SIZE / BASE_SIZE / 8, 1);
    bitmap_size = nrPages * PAGE_SIZE / BASE_SIZE / 8;

    for (i = 0; i <= NR_SIZES; i++) {
        free_lists[i] = NULL;
        free_list_ends[i] = NULL;
    }
}

void nvmalloc_exit(void)
{
    if (munmap((void*) start_address, nr_pages)) {
        perror("MUNMAP FAILED");
    }
}

void* nvmalloc(uint32_t size)
{
    uint32_t actualSize = 0;
    char* location;

    location = getFreeLocation(size + sizeof(header), &actualSize);

    if (!location) {
        return NULL;
    }

#ifdef D_XOR
    ((header*) location)->size = xorCompute(location, actualSize);
#else
#ifdef D_CRC
    ((header*) location)->size = crcCompute(location, actualSize);
#else
    ((header*) location)->size = actualSize;
#endif
#endif

    incrementTime();

    return (void*) (location + sizeof(header));
}

int nvfree(void* addr)
{
    char* location = ((char*) addr) - sizeof(header);
    uint32_t size;

    if (((header*) location)->size <= 0) {
        fprintf(stderr, "Header corruption detected!\n");
        exit(-1);
    }

#ifdef D_XOR
    size = xorGetSize(((header*) location)->size);
    if (xorCompute(location, size) != ((header*) location)->size) {
        fprintf(stderr, "Header corruption detected!\n");
        exit(-1);
    }
#else
#ifdef D_CRC
    size = crcGetSize(((header*) location)->size);
    if (crcCompute(location, size) != ((header*) location)->size) {
        fprintf(stderr, "Header corruption detected!\n");
        exit(-1);
    }

#else
    size = (uint32_t)(((header*) location)->size);
#endif
#endif
    putInDNAList(location, size);

    incrementTime();

    return 0;
}

void nvmalloc_print(void)
{
    unsigned i;

    for (i = 0; i < (end_address - start_address) / BASE_SIZE; i++)
    {
        unsigned index, mask;
        if (!(i % (PAGE_SIZE / BASE_SIZE)))
        {
            printf("\n");
        }
        index = i >> 3;
        mask = 1 << (i & 0x00000007);
        if (i >= (free_zone - start_address) / BASE_SIZE)
        {
            printf(" f ");
        }
        else if (bitmap[index] & mask)
        {
            printf(" o ");
        }
        else
        {
            printf(" _ ");
        }
    }
    printf("\n");

    for (i = 0; i <= NR_SIZES; i++)
    {
        list_head* lh;
        printf("List %u: ", i);
        lh = free_lists[i];
        while (lh != NULL)
        {
            printf("%llu -> ", lh->position / BASE_SIZE);
            lh = lh->next;
        }
        printf("NULL\n");
    }
}


