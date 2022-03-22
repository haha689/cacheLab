/**
 * @file mm.c
 * @brief A 64-bit struct-based segragated lists memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 * The structure of a free block of 16 bytes includes a header and a forward
 * pointer. For other free blocks, the strucutre includes a header, a backward
 * pointer, a forward pointer, and a footer. For allocated blocks, the structure
 * includes a header, payload, and necessary padding. The file is implemented
 * using segragated lists. There is an array of free lists. Each free list
 * corresponds to a size class. The size classes are specified inside the
 * function select_list. The free list containing blocks of 16 bytes is singly
 * linked. So we need to search through the list to remove a block.  All other
 * free lists are doubly linked. So list_add and list_rem are constant for them.
 * To add a free block or remove a free block, we call list_add or list_rem
 * respectively. List_rem and list_add are implemented using LIFO.
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Xinyi Lu <xinyilu@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/**
 * TODO: explain what chunksize is
 * (Must be divisible by dsize)
 * Chunksize is the smallest size that the heap will be lengthened by when
 * extend_heap is called.
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: explain what alloc_mask is
 * The mask used to extract the lowest bit of a header value. The lowest bit of
 * a header value indicates if the block is allocated.
 */
static const word_t alloc_mask = 0x1;

/**
 * TODO: explain what size_mask is
 * The mask used to extract the size of a block from a header value.
 */
static const word_t size_mask = ~(word_t)0xF;

/**
 * The mask used to extract the second bit of a header value. The second bit of
 * a header value indicates if the previous block is allocated.
 */
static const word_t prev_alloc_mask = 0x2;

/**
 * The mask used to extract the third bit of a header value. The third bit of
 * a header value indicates if the previous block has size 16.
 */
static const word_t prev_sixteen_mask = 0x4;

/**
 * The largest value that size_t can represent.
 */
static const size_t ULONG_MAX = 0xFFFFFFFFFFFFFFFF;

/**
 * We will compare at most 20 free blocks to find a block whose size is closest
 * to asize (asize is the size of the block we want to allocate).
 * Used in function find_fit.
 */
static const size_t max_num_of_comparisons = 20;

typedef struct block block_t;
/** @brief Represents the header and payload of one block in the heap */
struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.

    * For blocks with size 16, pointer1 is the forward pointer (next).
    * For other blocks, pointer1 is the backward pointer (prev).
    */
    union {
        block_t *pointer1;
        char payload[0];
    } U;
};

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/** An array of pointers to the first free blocks in the segragated list */
static block_t *list[15] = {0};
/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @param[in] prev_alloc True if the previous block is allocated
 * @param[in] prev_sixteen True if the previous block has size 16
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc,
                   bool prev_sixteen) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    if (prev_alloc) {
        word |= prev_alloc_mask;
    }
    if (prev_sixteen) {
        word |= prev_sixteen_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, U.payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->U.payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->U.payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 * @param[in] prev_alloc True if the previous block is allocated
 * @param[in] prev_sixteen True if the previous block has size 16
 */
static void write_epilogue(block_t *block, bool prev_alloc, bool prev_sixteen) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true, prev_alloc, prev_sixteen);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 * @param[in] prev_alloc True if the previous block is allocated
 * @param[in] prev_sixteen True if the previous block has size 16
 * @pre The block should not be NULL or the prologue.
 */
static void write_block(block_t *block, size_t size, bool alloc,
                        bool prev_alloc, bool prev_sixteen) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7 || size > 0);
    block->header = pack(size, alloc, prev_alloc, prev_sixteen);
    if (!alloc) {
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, alloc, prev_alloc, prev_sixteen);
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Returns if the size of the previous block is 16 given the header
 *        value of the current block.
 *
 * This is based on the third bit of the header value.
 *
 * @param[in] word
 * @return If the size of the previous block is 16
 */
static bool extract_prev_sixteen(word_t word) {
    return (bool)((word & prev_sixteen_mask) >> 2);
}

/**
 * @brief Returns if the size of the previous block is 16, based on the header
 *        of the current block.
 * @param[in] block
 * @return If the size of the previous block is 16
 */
static bool get_prev_sixteen(block_t *block) {
    return extract_prev_sixteen(block->header);
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 * @pre Used only when the size of the previous block is not 16. (Blocks with
 *      size 16 do not have a footer.))
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(!get_prev_sixteen(block));
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/**
 * @brief Returns the allocation status of the previous block given the header
 *        value of the current block.
 *
 * This is based on the second bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the previous block.
 */
static bool extract_prev_alloc(word_t word) {
    return (bool)((word & prev_alloc_mask) >> 1);
}

/**
 * @brief Returns the allocation status of the previous block, based on the
 *        header of the current block.
 * @param[in] block
 * @return The allocation status of the previos block.
 */
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}

/**
 * @brief Finds the previous consecutive block on the heap if the size of the
 *        previous consecutive block is 16.
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 * @pre Used only when the size of the previous block is 16.
 */
static block_t *find_prev_sixteen(block_t *block) {
    dbg_requires(get_prev_sixteen(block));
    return (block_t *)((char *)block - dsize);
}

/**
 * @brief Finds the second pointer stored in the payload. The second pointer
 *        stored in the payload is the forward pointer.
 * @param[in] block A block in the heap
 * @return A pointer to the second pointer stored in the payload of the block.
 * @pre Used only when the size of the block is not 16 and the block is free.
 */
static block_t **find_pointer2(block_t *block) {
    dbg_requires(block != NULL && get_size(block) != 16 && !get_alloc(block));
    return (block_t **)(&(block->U.pointer1) + 1);
}

/**
 * @brief Finds the index of the free list that the block with size
 *        asize should be stored in.
 * @param[in] asize The size of a block
 * @return The index of the free list that the block should be stored in.
 */
static size_t select_list(size_t asize) {
    size_t one = (size_t)1;
    if (asize == 16) {
        return 0;
    } else if (17 <= asize && asize <= 32) {
        return 1;
    } else if (33 <= asize && asize <= 48) {
        return 2;
    } else if (49 <= asize && asize <= (one << 6)) {
        return 3;
    } else if ((one << 6) + 1 <= asize && asize <= (one << 7)) {
        return 4;
    } else if ((one << 7) + 1 <= asize && asize <= (one << 8)) {
        return 5;
    } else if ((one << 8) + 1 <= asize && asize <= (one << 9)) {
        return 6;
    } else if ((one << 9) + 1 <= asize && asize <= (one << 10)) {
        return 7;
    } else if ((one << 10) + 1 <= asize && asize <= (one << 11)) {
        return 8;
    } else if ((one << 11) + 1 <= asize && asize <= (one << 12)) {
        return 9;
    } else if ((one << 12) + 1 <= asize && asize <= (one << 13)) {
        return 10;
    } else if ((one << 13) + 1 <= asize && asize <= (one << 14)) {
        return 11;
    } else if ((one << 14) + 1 <= asize && asize <= (one << 15)) {
        return 12;
    } else if ((one << 15) + 1 <= asize && asize <= (one << 16)) {
        return 13;
    } else {
        return 14;
    }
}

/**
 * @brief Add a free block into the corresponding free list. Implemented using
 *        LIFO.
 * @param[in] block A free block in the heap
 * @param[in] sixteen If the size of the block is 16 bytes
 * @pre The block is not NULL or allocated
 */
static void list_add(block_t *block, bool sixteen) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    size_t asize = get_size(block);
    size_t index = select_list(asize);
    // Make the block the first element in the list
    if (sixteen) {
        // Case 1: singly linked list
        // Set the forward pointer to list[index].
        block->U.pointer1 = list[index];
    } else {
        // Case 2: doubly linked list
        // Set backward pointer to NULL. Set forward pointer to list[index].
        block->U.pointer1 = NULL;
        block_t **pointer2 = find_pointer2(block);
        *pointer2 = list[index];
    }
    // If list[index] is empty
    if (list[index] == NULL) {
        list[index] = block;
        return;
    }
    // If list[index] is not empty and the block being added does not have size
    // 16 bytes, set the backward pointer of the next block in the list to
    // block
    if (!sixteen) {
        (list[index])->U.pointer1 = block;
    }
    list[index] = block;
}

/**
 * @brief Remove a free block from the corresponding free list. Implemented
 *        using LIFO.
 * @param[in] block A free block in the heap
 * @param[in] sixteen If the size of the block is 16 bytes
 * @pre The block is not NULL or allocated
 */
static void list_rem(block_t *block, bool sixteen) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    size_t asize = get_size(block);
    dbg_assert((sixteen && (asize == 16)) || !sixteen);
    size_t index = select_list(asize);
    // Case 1: remove a block of 16 bytes
    if (sixteen) {
        dbg_assert(index == 0);
        dbg_assert(list[index] != NULL);
        // If the list only contains one element (the block), just remove it.
        if (list[index] == block) {
            list[index] = block->U.pointer1;
            return;
        }
        // If there are more elements, we need to search through the list to
        // find the block, and then remove it. (The corresponding free list is
        // singly linked.)
        for (block_t *p = list[index]; p->U.pointer1 != NULL;
             p = p->U.pointer1) {
            if (p->U.pointer1 == block) {
                block_t *next = block->U.pointer1;
                p->U.pointer1 = next;
                return;
            }
        }
    }
    // Case 2: remove a block with size other than 16 bytes (The corresponding
    // list is doubly linked. So list_rem is constant time in this case.)
    dbg_assert(!sixteen);
    block_t *prev = block->U.pointer1;
    block_t **next = find_pointer2(block);
    dbg_assert(next != NULL);
    if (prev == NULL && *next == NULL) {
        // If the block is the only element in the list
        list[index] = NULL;
    } else if (prev == NULL) {
        // If the block is the first element in the list
        list[index] = *next;
        (*next)->U.pointer1 = NULL;
    } else if (*next == NULL) {
        // If the block is the last element in the list
        block_t **prev_next = find_pointer2(prev);
        *prev_next = NULL;
    } else {
        // If the block is in the middle of the list
        block_t **prev_next = find_pointer2(prev);
        dbg_assert(prev_next != NULL && (*next)->U.pointer1 != NULL);
        *prev_next = *next;
        (*next)->U.pointer1 = prev;
    }
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief coalesce the block with its previous consecutive block or the next
 *        consecutive block if any of them is free.
 * @param[in] block A free block in the heap
 * @return The block after coalescing
 * @pre The block should not be NULL or allocated
 */
static block_t *coalesce_block(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(!get_alloc(block));
    bool prev_alloc = get_prev_alloc(block);
    bool prev_sixteen = get_prev_sixteen(block);
    size_t size = get_size(block);
    block_t *next = find_next(block);
    bool next_alloc = get_alloc(next);
    size_t next_size = get_size(next);
    // We do not need to know the previous block if it is allocated.
    block_t *prev = NULL;
    size_t prev_size = 0;
    if (!prev_sixteen && !prev_alloc) {
        // If the previous block is free and with size other than 16 bytes,
        // we just find the previous block using its footer
        prev = find_prev(block);
        prev_size = get_size(prev);
    } else if (prev_sixteen && !prev_alloc) {
        // If the previous block is free and with size 16 bytes, we use pointer
        // aritimetic to find its header because it does not have a footer.
        prev = find_prev_sixteen(block);
        prev_size = 16;
    }
    if (prev_alloc && !next_alloc) {
        // Case 1: The previous block is allocated, the next is not
        bool next_sixteen = (next_size == 16);
        list_rem(next, next_sixteen);
        write_block(block, size + next_size, false, true, prev_sixteen);
        if (next_sixteen) {
            block_t *next_next = find_next(next);
            write_block(next_next, get_size(next_next), true, false, false);
        }
        list_add(block, false);
    } else if (!prev_alloc && next_alloc) {
        // Case 2: The next block is allocated, the previous is not
        list_rem(prev, prev_sixteen);
        bool prev_prev_sixteen = get_prev_sixteen(prev);
        write_block(prev, size + prev_size, false, true, prev_prev_sixteen);
        write_block(next, next_size, true, false, false);
        block = prev;
        list_add(block, false);
    } else if (!prev_alloc && !next_alloc) {
        // Case 3: Both previous block and next block are free
        list_rem(prev, prev_sixteen);
        list_rem(next, next_size == 16);
        bool prev_prev_sixteen = get_prev_sixteen(prev);
        write_block(prev, size + prev_size + next_size, false, true,
                    prev_prev_sixteen);
        if (next_size == 16) {
            block_t *next_next = find_next(next);
            write_block(next_next, get_size(next_next), true, false, false);
        }
        block = prev;
        list_add(block, false);
    } else if (prev_alloc && next_alloc) {
        // Case 4: Both previous block and next block are allocated
        if (size == 16) {
            list_add(block, true);
            write_block(next, next_size, true, false, true);
        } else {
            list_add(block, false);
            write_block(next, next_size, true, false, false);
        }
    }
    return block;
}

/**
 * @brief Extends the heap by the size given.
 * @param[in] size The size that the heap will be extended by
 * @return The block created by extending the heap
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    bool prev_sixteen = get_prev_sixteen(block);
    bool prev_alloc = get_prev_alloc(block);
    write_block(block, size, false, prev_alloc, prev_sixteen);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next, false, false);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief Split an allocated block into one allocated block and one free block
 *        if the size of the block is 16 bytes greater than asize.
 * @param[in] block An allocated block in the heap
 * @param[in] asize The size we want to allocate
 * @pre The block is allocated and has size greater or equal to asize. Asize is
 *      larger than 0.
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    dbg_requires(asize > 0 && asize <= get_size(block));
    /* TODO: Can you write a precondition about the value of asize? */

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        bool prev_sixteen = get_prev_sixteen(block);
        bool prev_alloc = get_prev_alloc(block);
        write_block(block, asize, true, prev_alloc, prev_sixteen);

        block_next = find_next(block);
        write_block(block_next, block_size - asize, false, true, asize == 16);
        block_t *block_next_next = find_next(block_next);
        write_block(block_next_next, get_size(block_next_next),
                    get_alloc(block_next_next), false,
                    (block_size - asize) == 16);
        list_add(block_next, block_size - asize == 16);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief Searches through free lists to find a block with size >= asize. If no
 *        such block exists, return NULL. It is implemented using better fit
 *        algorithm. It searches at most max_num_of_comparisons blocks and
 *        returns the block whose size is closest to asize.
 * @param[in] asize The size we want to allocate
 * @return A free block with size >= asize
 */
static block_t *find_fit(size_t asize) {
    block_t *block;
    size_t index = select_list(asize);
    size_t counter = 0;
    size_t difference = ULONG_MAX;
    block_t *better_fit = NULL;
    if (index == 0) {
        // If the size of the block is 16 bytes, block->U.pointer1 is the
        // forward pointer
        for (block = list[index]; block != NULL; block = block->U.pointer1) {
            return block;
        }
    } else {
        // If the size of the block is not 16 bytes, *(find_pointer2(block)) is
        // the forward pointer
        for (block = list[index]; block != NULL;
             block = *(find_pointer2(block))) {
            dbg_assert(!(get_alloc(block)));
            dbg_assert(find_pointer2(block) != NULL);
            if (asize <= get_size(block) &&
                get_size(block) - asize < difference) {
                better_fit = block;
                difference = get_size(block) - asize;
            }
            counter++;
            if (counter >= max_num_of_comparisons && better_fit != NULL) {
                return better_fit;
            }
        }
    }
    // We do not need to do more researches if better_fit != NULL because
    // according to the size classes corresponding to the free lists, the size
    // of blocks in list[index+1] to list[16] must be greater than the size of
    // better_fit. In this case, better_fit is the best fit we can find.
    if (better_fit != NULL) {
        return better_fit;
    }
    for (size_t i = index + 1; i < 15; i++) {
        for (block = list[i]; block != NULL; block = *(find_pointer2(block))) {
            dbg_assert(!(get_alloc(block)));
            dbg_assert(find_pointer2(block) != NULL);
            if (get_size(block) - asize < difference) {
                better_fit = block;
                difference = get_size(block) - asize;
            }
            counter++;
            if (counter >= max_num_of_comparisons && better_fit != NULL) {
                return better_fit;
            }
        }
        // Similar logic as above
        if (better_fit != NULL) {
            return better_fit;
        }
    }
    if (better_fit != NULL) {
        return better_fit;
    }
    return NULL; // no fit found
}

/**
 * @brief Checks if the heap and segragated free lists are valid
 * @param[in] line The line number of the code where mm_checkheap is called
 * @return If the heap and segragated free lists are valid
 */
bool mm_checkheap(int line) {
    block_t *block;
    char *epilogue = mem_heap_hi() - 7;
    char *prologue = mem_heap_lo();
    if (!(*((word_t *)prologue) == 0x3 && get_alloc((block_t *)epilogue))) {
        dbg_printf("%d, epilogue/prologue error \n", line);
        return false;
    }
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        size_t size = get_size(block);
        bool alloc = get_alloc(block);
        bool prev_alloc = get_prev_alloc(block);
        bool prev_sixteen = get_prev_sixteen(block);
        if (size % 16 != 0 && size < 16) {
            dbg_printf("%d, alignment error\n", line);
            return false;
        }
        if (!alloc && size != 16) {
            word_t *footer = header_to_footer(block);
            if (pack(size, alloc, prev_alloc, prev_sixteen) != *(footer)) {
                dbg_printf("%d, header/footer error\n", line);
                dbg_printf("header: %lx, footer : %lx\n",
                           pack(size, alloc, prev_alloc, prev_sixteen),
                           *(footer));
                return false;
            }
        }
        block_t *next = find_next(block);
        if (prev_alloc) {
            if ((char *)next > ((char *)mem_heap_hi()) - 7) {
                dbg_printf("%d, block out of heap boundaries\n", line);
                return false;
            }
        } else {
            block_t *prev;
            if (prev_sixteen) {
                prev = find_prev_sixteen(block);
            } else {
                prev = find_prev(block);
            }
            if (prev != NULL && (prev < heap_start ||
                                 (char *)next > ((char *)mem_heap_hi()) - 7)) {
                dbg_printf("%d, block out of heap boundaries\n", line);
                return false;
            }
        }
        if (!alloc) {
            if (!prev_alloc || !get_alloc(next)) {
                dbg_printf("prev: %d, next: %d\n", (int)prev_alloc,
                           (int)get_alloc(next));
                dbg_printf("%d, consecutive free blocks\n", line);
                return false;
            }
        }
        bool next_prev_alloc = get_prev_alloc(next);
        bool next_prev_sixteen = get_prev_sixteen(next);
        if ((alloc && !next_prev_alloc) || (!alloc && next_prev_alloc)) {
            dbg_printf("%d, alloc and next_prev_alloc doesn't match\n", line);
        }
        if ((size == 16 && !next_prev_sixteen) ||
            (size != 16 && next_prev_sixteen)) {
            dbg_printf("%d, size and next_prev_sixteen doesn't match\n", line);
        }
    }
    for (block = list[0]; block != NULL; block = block->U.pointer1) {
        if (get_alloc(block)) {
            dbg_printf("free list [0] contains allocated blocks");
            return false;
        }
        if (get_size(block) != 16) {
            dbg_printf("list[0] contain blocks with size != 16");
            return false;
        }
    }
    for (int i = 1; i < 15; i++) {
        for (block = list[i]; block != NULL; block = *(find_pointer2(block))) {
            if (get_alloc(block)) {
                dbg_printf("free list contains allocated blocks");
                return false;
            }
            block_t *prev = block->U.pointer1;
            block_t **next = find_pointer2(block);
            dbg_assert(next != NULL);
            if (prev == NULL && *next != NULL && (*next)->U.pointer1 != block) {
                dbg_printf("Backward pointer doesn't match");
                return false;
            }
            if (prev != NULL && *next == NULL &&
                *(find_pointer2(prev)) != block) {
                dbg_printf("Forward pointer doesn't match");
                return false;
            }
            if (prev != NULL && *next != NULL) {
                if (*(find_pointer2(prev)) != block) {
                    dbg_printf("forward pointer doesn't match");
                    return false;
                }
                if ((*next)->U.pointer1 != block) {
                    dbg_printf("backward pointer doesn't match");
                    return false;
                }
            }
        }
    }
    return true;
}

/**
 * @brief Initializes the heap to include an epilogue, a prologue, and a free
 *        block of chunksize bytes
 * @return If the heap is successfully initialized
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, true, true, false); // Heap prologue (block footer)
    start[1] = pack(0, true, true, false); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);
    // Initialize the segregated free lists
    memset(list, 0, 120);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief Allocates a block with payload size equal to size
 * @param[in] size The size of the payload we want to allocate
 * @return A pointer to the payload we allocate.
 *         Returns NULL if we fail to allocate.
 * @pre The heap is valid
 * @ensure The heap is valid
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    list_rem(block, block_size == 16);
    bool prev_sixteen = get_prev_sixteen(block);
    bool prev_alloc = get_prev_alloc(block);
    write_block(block, block_size, true, prev_alloc, prev_sixteen);

    // Update the next consecutive block
    block_t *next = find_next(block);
    write_block(next, get_size(next), get_alloc(next), true, block_size == 16);

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief free a block with payload that bp points to
 * @param[in] bp A pointer to the payload of the block that we want to free
 * @pre The heap is valid
 * @ensure The heap is valid
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    bool prev_sixteen = get_prev_sixteen(block);
    bool prev_alloc = get_prev_alloc(block);
    write_block(block, size, false, prev_alloc, prev_sixteen);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief Frees the block corresponding to ptr and allocates a new block of size
 *        bytes
 * @param[in] ptr A pointer to the payload of the block that we want to realloc
 * @param[in] size The size of the new block that we want to allocate
 * @return A pointer to the payload of the newly allocated block.
 *         Returns NULL if we fail to allocate.
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief Allocates a block with payload of size*elements bytes and initializes
 *        the field of the block to zero
 * @param[in] elements The number of elements we want to allocate
 * @param[in] size The size of each element
 * @return A pointer to the payload of the newly allocated block
 *         Returns NULL if we fail to allocate.
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
