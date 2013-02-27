#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <iostream>
#include <sys/time.h>
#include <stdint.h>
#include <xmmintrin.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

using namespace std;

static __inline__ unsigned long rdtsc()
{
      unsigned hi, lo;
        __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
          return ( (unsigned long)lo)|( ((unsigned long)hi)<<32 );
}

inline void clflush(volatile char* __p)
{
    asm volatile("clflush %0" : "+m" (__p));
}

inline void flushRange(char* start, char* end)
{
    unsigned CACHE_LINE_SIZE = 64;
    for (char* ptr = start; ptr < end; ptr += CACHE_LINE_SIZE)
    {
        clflush(ptr);
    }
}

inline void mfence()
{
    asm volatile("mfence":::"memory");
}

unsigned* random_permutation(unsigned n)
{
    unsigned* perm = (unsigned*)malloc(n * sizeof(unsigned));
    for (unsigned i = 0; i < n; i++)
    {
        perm[i] = i;
    }
    for (unsigned i = 0; i < n; i++)
    {
        unsigned p = rand() % (n - i) + i;
        unsigned aux = perm[p];
        perm[p] = perm[i];
        perm[i] = aux;
    }
    return perm;
}

#define DEV_NPAGES 4000
#define PERM_GROUP 1000

//char gbuf[20 * 256 * 4096];

int main(int argc, char* argv[])
{
    int fd;
    uint64_t* vadr;
    volatile uint64_t* queue;
    int len = DEV_NPAGES * getpagesize();//3 * DEV_NPAGES * getpagesize();
    volatile unsigned* read;
    volatile unsigned* write;
    unsigned size, next;

    if (argc != 3)
    {
        cerr << "Usage: randwrite write_unit_size number_of_units_to_write" << endl;
        return -1;
    }
    srand(0);
    unsigned u = atoi(argv[1]);
    unsigned n = atoi(argv[2]);
    cout << u << " de " << n << " ori" << endl;
    char* buffer = (char*)malloc(u);

    if ((fd=open("node", O_RDWR | O_SYNC)) < 0)
    {
        perror("open");
        exit(-1);
    }

    vadr = (unsigned long*) mmap(0, len, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);

    if (vadr == MAP_FAILED)
    {
        perror("async mprotect device mmap failed");
        exit(-1);
    }

    read = (unsigned*) (vadr + 8);
    write = (unsigned*) (vadr + 16);

    // init async mprotect for this process
    vadr[0] = getpid();
    size = DEV_NPAGES * getpagesize() / sizeof(uint64_t) - 24;
    queue = vadr + 24;


    char* mem = (char*)mmap(NULL, u * n, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, 0, 0);
    if (mem == MAP_FAILED)
    {
        perror("mmap failed");
        return -1;
    }
    cout << "RDTSC: " << rdtsc() << endl;
    unsigned* perm = random_permutation(PERM_GROUP);

    timeval start, end;


    for (unsigned i = 0; i < n; i++)
    {
        mem[i * u] = 0;
    }

    gettimeofday(&start, NULL);

    unsigned counter = 0;
    unsigned local_read = *read;

    for (unsigned i = 0; i < n; i++)
    {
        memcpy(mem + ((i / PERM_GROUP)  * PERM_GROUP + perm[i % PERM_GROUP]) * u, buffer, u);

/*        if (mprotect(mem + ((i / PERM_GROUP)  * PERM_GROUP  + perm[i % PERM_GROUP]) * u, 4096, PROT_READ) != 0)
        {
            perror("mprotect2 failed");
            return -1;
        }*/

        next = (*write + 2) % size;

        if (next == local_read)
        {
            local_read = *read;
            //counter++;
        }

        if (next != local_read)
        {
            queue[*write] = (unsigned long)(mem + ((i / PERM_GROUP)  * PERM_GROUP  + perm[i % PERM_GROUP]) * u);
            queue[*write + 1] = rdtsc();
            *write = next;
            counter++;
        }
        else
        {
            //printf("No more space in the queue\n");
        }
    }
    cout << "*write = " << *write << endl;
    gettimeofday(&end, NULL);

    cout << "Total time: " << (end.tv_sec - start.tv_sec) * 1000 +
                              (end.tv_usec - start.tv_usec) / 1000 << " ms" << endl;

//    usleep(500000);

    cout << "counter = " << counter << endl;

/*
    unsigned long* values = vadr + 2 * DEV_NPAGES * getpagesize() / sizeof(unsigned long);

    for (unsigned i = 0; i < n; i++)
    {
        cout << values[i] << endl;
    }

*/

/*    for (unsigned i = 0; i < n; i++)
    {
        mprotect(mem + i * u, 4096, PROT_READ | PROT_WRITE);
    }
    mem[5 * u + 3] = 0;
    */

    munmap(vadr, len);
    close(fd);
    munmap(mem, u * n);

    return 0;
}



