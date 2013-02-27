#include <linux/kernel.h>
#include <linux/version.h>
#include <linux/init.h>
#include <linux/module.h>
#include <linux/fs.h>
#include <linux/cdev.h>
#include <linux/slab.h>
#include <linux/vmalloc.h>
#include <linux/mm.h>
#include <linux/sched.h>
#include <linux/kthread.h>
#ifdef MODVERSIONS
#include <linux/modversions.h>
#endif

#include <linux/mman.h>

#include <asm/io.h>
#include <linux/hrtimer.h>


MODULE_DESCRIPTION("async memory protect device");
MODULE_AUTHOR("Iulian Moraru <iulian@cs.cmu.edu>");
MODULE_LICENSE("Dual BSD/GPL");


// character device structures
static dev_t asyncp_dev;
static struct cdev asyncp_cdev;

// methods of the character device
static int asyncp_open(struct inode *inode, struct file *filp);
static int asyncp_release(struct inode *inode, struct file *filp);
static int asyncp_mmap(struct file *filp, struct vm_area_struct *vma);

// the file operations, i.e. all character device methods
static struct file_operations asyncp_fops = {
    .open = asyncp_open,
    .release = asyncp_release,
    .mmap = asyncp_mmap,
    .owner = THIS_MODULE,
};

//-------- INTERNAL DATA -------------

// length of the device memory area
#define NPAGES 15000

// thread wait time in milliseconds
#define THREAD_WAIT_TIME_MS 4

// pointer to the vmalloc'd area - alway page aligned
static unsigned long* device_memory;

// shared memory read and write pointers
static volatile unsigned* read;
static volatile unsigned* write;
//-------------------------------------
extern volatile unsigned long *asyncp_unprot_queue;



static /*__inline__*/ unsigned long rdtsc(void)
{
      unsigned long hi, lo;
      __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
          return ( (unsigned long)lo)|( ((unsigned long)hi)<<32 );
}

static int asyncp_open(struct inode *inode, struct file *filp)
{
    return 0;
}

static int asyncp_release(struct inode *inode, struct file *filp)
{
    return 0;
}

// helper function, mmap's the vmalloc'd area which is not physically contiguous
int asyncp_vmem(struct file *filp, struct vm_area_struct *vma)
{
    int ret;
    long length = vma->vm_end - vma->vm_start;
    unsigned long start = vma->vm_start;
    char* vmalloc_area_ptr = (char*) device_memory;
    unsigned long pfn;

    /* check length - do not allow larger mappings than the number of
       pages allocated */
    if (length > NPAGES * PAGE_SIZE)
    {
        return -EIO;
    }

    /* loop over all pages, map each page individually */
    while (length > 0)
    {
        pfn = vmalloc_to_pfn(vmalloc_area_ptr);
        if ((ret = remap_pfn_range(vma, start, pfn, PAGE_SIZE, PAGE_SHARED)) < 0)
        {
            return ret;
        }
        start += PAGE_SIZE;
        vmalloc_area_ptr += PAGE_SIZE;
        length -= PAGE_SIZE;
    }
    return 0;
}

// character device mmap method
static int asyncp_mmap(struct file *filp, struct vm_area_struct *vma)
{
    if (vma->vm_pgoff == 0)
    {
        return asyncp_vmem(filp, vma);
    }

    return -EIO;
}

static unsigned long prot_read_vm_flags;

// helper function for changing the protection of a page
inline static void asyncp_change_page_protection(struct mm_struct* mm, unsigned long paddr, unsigned long end, unsigned do_not_flush_tlb)
{
     unsigned long nstart, tmp;
     struct vm_area_struct *vma, *prev;

     //end = paddr + 4096;

     if (!mm)
     {
         return;
     }

     //down_write(&mm->mmap_sem);

     vma = find_vma_prev(mm, paddr, &prev);
     if (!vma)
         goto out;
     if (vma->vm_start > paddr)
         goto out;

     if (paddr > vma->vm_start)
         prev = vma;

     for (nstart = paddr; ; )
     {
         unsigned long newflags;

         /* Here we know that  vma->vm_start <= nstart < vma->vm_end. */

         newflags = prot_read_vm_flags | (vma->vm_flags & ~(VM_READ | VM_WRITE | VM_EXEC));

         /* newflags >> 4 shift VM_MAY% in place of VM_% */
         if ((newflags & ~(newflags >> 4)) & (VM_READ | VM_WRITE | VM_EXEC))
         {
             printk(KERN_DEBUG "EACCESS error\n");
             goto out;
         }

         //error = security_file_mprotect(vma, reqprot, prot);
         //if (error)
         //    goto out;

         tmp = vma->vm_end;
         if (tmp > end)
             tmp = end;
         if (mprotect_fixup(vma, &prev, nstart, tmp, newflags, do_not_flush_tlb))
         {
             printk(KERN_DEBUG "mprotect_fixup error\n");
             goto out;
         }

         nstart = tmp;

         if (nstart < prev->vm_end)
             nstart = prev->vm_end;
         if (nstart >= end)
             goto out;

         vma = prev->vm_next;
         if (!vma || vma->vm_start != nstart)
         {
             printk(KERN_DEBUG "ENOMEM error\n");
             goto out;
         }
     }
out:
     //up_write(&mm->mmap_sem);
     return;
}

static inline int partition(unsigned long* vector, int start, int end)
{
    int pp = (end - start + 1) / 2 + start;
    unsigned long pivot = vector[pp];
    int index, i;

    vector[pp] = vector[end];
    vector[end] = pivot;
    index = start;
    for (i = start; i < end; i++)
    {
        if (vector[i] < pivot)
        {
            unsigned long aux = vector[index];
            vector[index] = vector[i];
            vector[i] = aux;
            index++;
        }
    }
    vector[end] = vector[index];
    vector[index] = pivot;
    return index;
}

static void quick_sort(unsigned long* vector, int start, int end, int depth)
{
    int m;

    if (start >= end)
    {
        return;
    }
    else if (depth % 20 == 0)
    {
        yield();
    }

    //printk(KERN_DEBUG "depth: %d\n", depth);

    m = partition(vector, start, end);

    quick_sort(vector, start, m - 1, depth + 1);
    quick_sort(vector, m + 1, end, depth + 1);
}

static int *beg, *end;

/*
 * Code from http://alienryderflex.com/quicksort/
 */
static void quick_sort_nonrec(unsigned long* arr, int elements)
{
#define  MAX_LEVELS  10000
    unsigned long piv;
    int i=0, L, R ;

    beg[0]=0; end[0]=elements;
    while (i>=0) {
        L=beg[i]; R=end[i]-1;
        if (i % 50 == 0)
            yield();
        if (L<R) {
            piv=arr[L]; if (i==MAX_LEVELS-1) return;
            while (L<R) {
                while (arr[R]>=piv && L<R) R--; if (L<R) arr[L++]=arr[R];
                while (arr[L]<=piv && L<R) L++; if (L<R) arr[R--]=arr[L];
            }
            arr[L]=piv; beg[i+1]=L+1; end[i+1]=end[i]; end[i++]=L;
        }
        else {
            i--;
        }
    }
}

static struct task_struct *asyncp_thread;

static int asyncp_scan_thread(void *data)
{
    struct task_struct* task = NULL;
    struct mm_struct* mm = NULL;
    pid_t pid;
    unsigned long* queue = device_memory + 32;
    unsigned queue_size = NPAGES / 3 * PAGE_SIZE / sizeof(unsigned long) - 32;
    unsigned long* vector = device_memory + NPAGES / 3 * PAGE_SIZE / sizeof(unsigned long);
    unsigned long* timestamps = vector + NPAGES / 3 * PAGE_SIZE / sizeof(unsigned long);
    unsigned counter = 0, counter2 = 0, tscounter = 0;
    cpumask_t cpumask;
    struct timespec timeout;

    //set_user_nice(current, 5);
    //set_current_state(TASK_INTERRUPTIBLE);

    cpumask_empty(&cpumask);
    cpumask_set_cpu(0, &cpumask);
    sched_setaffinity(current->pid, &cpumask);

    while (1)
    {
        if (kthread_should_stop())
        {
            return 0;
        }

        if (!device_memory[0])
        {
            mm = NULL;
        }
        else if (device_memory[0] > 1)
        {
            pid = device_memory[0];
            printk(KERN_DEBUG "Processed %u pages\n", counter);
            counter = 0;
            printk(KERN_DEBUG "Called TLB flush %u times\n", counter2);
            counter2 = 0;
            printk(KERN_DEBUG "ASYNCPROT: New pid: %u\n", pid);
            task = pid_task(find_pid_ns(pid, &init_pid_ns), PIDTYPE_PID);
            if (task)
            {
                mm = get_task_mm(task);
            }

/*            if (tscounter > 0)
            {
                unsigned i;
                unsigned long sum = 0, max = 0, min = 0xFFFFFFFFFFFFFFFF;
                unsigned min_pos = 0;

                for (i = 0; i < tscounter; i++)
                {
                    if (min > timestamps[i])
                    {
                        min = timestamps[i];
                        min_pos = i;
                    }
                    if (max < timestamps[i])
                    {
                        max = timestamps[i];
                    }
                    sum += timestamps[i];
                }
                printk(KERN_DEBUG "Total wait: %lu\n", sum);
                printk(KERN_DEBUG "Total requests: %u\n", tscounter);
                printk(KERN_DEBUG "Max wait: %lu\n", max);
                printk(KERN_DEBUG "Min wait: %lu\n", min);
                printk(KERN_DEBUG "min pos: %u\n", min_pos);
                printk(KERN_DEBUG "rdtsc: %lu\n", rdtsc());
                tscounter = 0;
            }
*/

            device_memory[0] = 1;
        }

        if (mm)
        {
            unsigned next = *read;
            unsigned local_write = *write;
/*
            unsigned processed = 0, i;
            unsigned long tsc = rdtsc();
            unsigned long paddr;
*/
            int vector_size = 0;

            while (next != local_write)
            {
                vector[vector_size++] = queue[next];
                //timestamps[tscounter++] = queue[next + 1];
                next = (next + 1) % queue_size;
                //next = (next + 1) % queue_size;
                if (next == local_write)
                {
                    local_write = *write;
                }
                *read = next;
                //counter++;
            }

            if (vector_size > 0)
            {
                unsigned long start;
                volatile unsigned long tsc;
                unsigned i, j;

                //quick_sort(vector, 0, vector_size - 1, 0);
                quick_sort_nonrec(vector, vector_size);

/*                for (i = 0; i < vector_size - 1; i++)
                {
                    yield();
                    for (j = i + 1; j < vector_size; j++)
                    {
                        if (vector[i] > vector[j])
                        {
                            unsigned long aux = vector[i];
                            vector[i] = vector[j];
                            vector[j] = aux;
                        }
                    }
                }
*/
                start = vector[0];

                down_write(&mm->mmap_sem);

                for (i = 0; i < vector_size - 1; i++)
                {
                    if ((vector[i + 1] != vector[i]) &&
                        (vector[i + 1] - vector[i] != PAGE_SIZE))
                    {
                        asyncp_change_page_protection(mm, start, vector[i] + PAGE_SIZE, 1);
                        start = vector[i + 1];
                        //counter++;
                    }
                    counter++;
                }
                asyncp_change_page_protection(mm, start, vector[vector_size - 1] + PAGE_SIZE, 0);
                //tsc = rdtsc();
                counter++;
                counter2++;

                up_write(&mm->mmap_sem);

/*
                for (i = tscounter - vector_size; i < tscounter; i++)
                {
                    timestamps[i] = tsc - timestamps[i];
                }*/
            }
        }

        schedule_timeout_interruptible(10);//msecs_to_jiffies(THREAD_WAIT_TIME_MS));
        //timeout = ns_to_timespec(10 * 1000);
        //hrtimer_nanosleep(&timeout, NULL, HRTIMER_MODE_REL, CLOCK_REALTIME);
    }
    do_exit(0);
}

// module initialization - called at module load time
static int __init asyncp_init(void)
{
    int ret = 0;
    int i;

    beg = (int*)vmalloc(MAX_LEVELS * sizeof(int));
    end = (int*)vmalloc(MAX_LEVELS * sizeof(int));

    /* allocate a memory area with vmalloc. */
    if ((device_memory = (unsigned long *)vmalloc(NPAGES * PAGE_SIZE)) == NULL)
    {
        ret = -ENOMEM;
        goto out;
    }

    /* get the major number of the character device */
    if ((ret = alloc_chrdev_region(&asyncp_dev, 0, 1, "asyncp")) < 0)
    {
        printk(KERN_ERR "could not allocate major number for asyncp\n");
        goto out_vfree;
    }

    /* initialize the device structure and register the device with the kernel */
    cdev_init(&asyncp_cdev, &asyncp_fops);
    if ((ret = cdev_add(&asyncp_cdev, asyncp_dev, 1)) < 0)
    {
        printk(KERN_ERR "could not allocate chrdev for asyncp\n");
        goto out_unalloc_region;
    }

    /* mark the pages reserved */
    for (i = 0; i < NPAGES * PAGE_SIZE; i+= PAGE_SIZE)
    {
        SetPageReserved(vmalloc_to_page((void *)(((unsigned long)device_memory) + i)));
    }

    /* init device memory */
    device_memory[0] = 1;

    read = (unsigned*) (device_memory + 8);
    write = (unsigned*) (device_memory + 16);
    *read = 0;
    *write = 0;

    asyncp_unprot_queue = device_memory + 24;

    prot_read_vm_flags = calc_vm_prot_bits(PROT_READ);

    asyncp_thread = kthread_run(asyncp_scan_thread, NULL, "asyncp_kthread");

    printk(KERN_DEBUG "Asyncp module started.\n");

    return ret;

out_unalloc_region:
    unregister_chrdev_region(asyncp_dev, 1);
out_vfree:
    vfree(device_memory);
out:
    return ret;
}

/* module unload */
static void __exit asyncp_exit(void)
{
    int i;

    /* stop thread */
    kthread_stop(asyncp_thread);

    /* remove the character deivce */
    cdev_del(&asyncp_cdev);
    unregister_chrdev_region(asyncp_dev, 1);

    /* unreserve the pages */
    for (i = 0; i < NPAGES * PAGE_SIZE; i+= PAGE_SIZE)
    {
        ClearPageReserved(vmalloc_to_page((void *)(((unsigned long)device_memory) + i)));
    }

    /* free the memory areas */
    vfree(device_memory);

    vfree(beg);
    vfree(end);

    printk(KERN_DEBUG "Asyncp module stopped.\n");
}

module_init(asyncp_init);
module_exit(asyncp_exit);
