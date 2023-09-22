/**
 * Do not submit your assignment with a main function in this file.
 * If you submit with a main function in this file, you will get a zero.
 */
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "debug.h"
#include "sfmm.h"

static sf_block* epiloguePtr = NULL;
static sf_block* prologueStart = NULL;

static sf_block* predecessorBlockFetcher(sf_block *block) {
    sf_footer *predecessorFooter = (sf_footer *)((char *)block - sizeof(sf_footer));
    size_t predecessorSize = *predecessorFooter & ~0x7;

    if (predecessorSize == 0 || ((char *)block - predecessorSize) < (char *)sf_mem_start() || ((char *)block - predecessorSize) > (char *)sf_mem_end()) {
        return NULL;
    }

    return (sf_block *)((char *)block - predecessorSize);
}

static sf_block* successorBlockFetcher(sf_block *block) {
    if((block->header & ~0x7) == 0 || ((char *)block + (block->header & ~0x7)) < (char *)sf_mem_start() || ((char *)block + (block->header & ~0x7)) > (char *)sf_mem_end()) {
        return NULL;
    }

    return (sf_block *)(((char *)block) + (block->header & ~0x7));
}

void *sf_malloc(size_t size) {
    int numOfQuickLists = NUM_QUICK_LISTS;
    int numOfFreeLists = NUM_FREE_LISTS;
    if(size == 0) {
        return NULL;
    }

    if(sf_mem_start() == sf_mem_end()) {
        prologueStart = sf_mem_grow();
        prologueStart->header = 32 | THIS_BLOCK_ALLOCATED;

        epiloguePtr = (sf_block*)((char*) sf_mem_end() - 8);
        epiloguePtr->header = 0 | THIS_BLOCK_ALLOCATED;

        sf_block* freeBlock = (sf_block*)((char*) prologueStart + 32);
        freeBlock->header = (PAGE_SZ - 40);
        freeBlock->header |= PREV_BLOCK_ALLOCATED;

        sf_footer* footerPtr = (sf_footer*)((char*) freeBlock + PAGE_SZ - 40 - 8);
        *(footerPtr) = freeBlock->header;

        freeBlock->body.links.prev = NULL;
        freeBlock->body.links.next = NULL;

        int m = 0;
        while(m < numOfFreeLists) {
            sf_free_list_heads[m].body.links.prev = &sf_free_list_heads[m];
            sf_free_list_heads[m].body.links.next = &sf_free_list_heads[m];
            m++;
        }

        sf_free_list_heads[numOfFreeLists - 1].body.links.next = freeBlock;
        sf_free_list_heads[numOfFreeLists - 1].body.links.prev = freeBlock;
        freeBlock->body.links.next = &sf_free_list_heads[numOfFreeLists - 1];
        freeBlock->body.links.prev = &sf_free_list_heads[numOfFreeLists - 1];

        int j = 0;
        while(j < numOfQuickLists) {
            sf_quick_lists[j].length = 0;
            sf_quick_lists[j].first = NULL;
            j++;
        }
    }

    size_t totalSize = 32;

    if(size <= 24) {
        totalSize = 32;
    }
    else {
        if((size + 8) % 8 == 0) {
            totalSize = size + 8;
        }
        else {
            totalSize = (size + 8) + (8 - ((size + 8) % 8));

        }
    }

    size_t quickIndex = (totalSize - 32) / 8;
    if (quickIndex < numOfQuickLists) {
        if (sf_quick_lists[quickIndex].length > 0) {
            sf_block *quickListblock = sf_quick_lists[quickIndex].first;
            quickListblock->header |= THIS_BLOCK_ALLOCATED;
            sf_quick_lists[quickIndex].first = quickListblock->body.links.next;
            quickListblock->header &= ~IN_QUICK_LIST;
            sf_quick_lists[quickIndex].length -= 1;
            quickListblock->header = (quickListblock->header & 0x7) | (quickListblock->header & ~0x7);
            return quickListblock->body.payload;
        }
    }

    size_t freeListIndex = 0;
    while (freeListIndex < (numOfFreeLists - 1)) {
        if (totalSize <= (32 * (1 << freeListIndex))) {
            break;
        }
        freeListIndex++;
    }

    int loopIndex = freeListIndex;
    while(loopIndex < numOfFreeLists) {
        sf_block *indexHead = &sf_free_list_heads[loopIndex];
        sf_block *currentBlock = indexHead->body.links.next;
        for(;(!(currentBlock == indexHead));) {
            if ((int)((currentBlock->header & ~0x7) - totalSize) >= 32) {
                currentBlock->body.links.next->body.links.prev = currentBlock->body.links.prev;
                size_t dividedSize = (currentBlock->header & ~0x7) - totalSize;
                currentBlock->body.links.prev->body.links.next = currentBlock->body.links.next;

                currentBlock->header = (currentBlock->header & 0x7) | (totalSize);
                sf_block *theNextBlockPtr = successorBlockFetcher(currentBlock);

                size_t alloc_bit = (currentBlock->header & 0x1);

                theNextBlockPtr->header = dividedSize;

                if(alloc_bit == 0x1) {
                    theNextBlockPtr->header |= PREV_BLOCK_ALLOCATED;
                }
                else {
                    theNextBlockPtr->header &= ~PREV_BLOCK_ALLOCATED;
                }

                theNextBlockPtr->header &= ~IN_QUICK_LIST;
                theNextBlockPtr->header &= ~THIS_BLOCK_ALLOCATED;

                sf_footer *newFooterPtr = (sf_footer *)((char *)theNextBlockPtr + dividedSize - sizeof(sf_footer));
                *newFooterPtr = theNextBlockPtr->header;

                sf_block *newBlock = theNextBlockPtr;

                currentBlock->header = (currentBlock->header & 0x7) | totalSize;
                currentBlock->header |= THIS_BLOCK_ALLOCATED;

                currentBlock->header &= ~IN_QUICK_LIST;

                newBlock->header = (newBlock->header & 0x7) | (newBlock->header & ~0x7);
                newBlock->header &= ~THIS_BLOCK_ALLOCATED;
                newBlock->header &= ~IN_QUICK_LIST;

                size_t theBlockSize = newBlock->header & ~0x7;
                size_t blockIndex = 0;
                while(theBlockSize >= 0 && blockIndex < (NUM_FREE_LISTS - 1)) {
                    if (theBlockSize <= (32 * (1 << blockIndex))) {
                        uintptr_t mySize = sizeof(theBlockSize);
                        mySize = mySize;
                        //debug("%zu", mySize);
                        break;
                    }
                    blockIndex++;
                }
                sf_block *indexBlock = &sf_free_list_heads[blockIndex];
                size_t indexBlockSize = sizeof(indexBlock);
                sf_block *next_block = indexBlock->body.links.next;

                newBlock->body.links.next = next_block;
                indexBlockSize = sizeof(indexBlock);
                newBlock->body.links.prev = indexBlock;

                indexBlock->body.links.next = newBlock;
                indexBlockSize = sizeof(indexBlock);
                next_block->body.links.prev = newBlock;
                //debug("%zu", indexBlockSize);
                indexBlockSize = indexBlockSize;

                if(successorBlockFetcher(currentBlock) != NULL) {
                    (successorBlockFetcher(currentBlock))->header |= PREV_BLOCK_ALLOCATED;
                    sf_footer *newFooterPtr = (sf_footer *)((char *)successorBlockFetcher(currentBlock) + ((successorBlockFetcher(currentBlock)->header) & ~0x7) - sizeof(sf_footer));
                    *newFooterPtr = (successorBlockFetcher(currentBlock))->header;
                }

                sf_block *last_block = predecessorBlockFetcher(epiloguePtr);
                if(last_block == NULL) {
                    epiloguePtr->header |= PREV_BLOCK_ALLOCATED;
                    return currentBlock->body.payload;
                }

                if ((last_block->header & 0x1) == 0x1) {
                    epiloguePtr->header |= PREV_BLOCK_ALLOCATED;
                } else {
                    epiloguePtr->header &= ~PREV_BLOCK_ALLOCATED;
                }
                return currentBlock->body.payload;
            }
            else if ((int)(currentBlock->header & ~0x7) >= (int)totalSize) {
                currentBlock->body.links.next->body.links.prev = currentBlock->body.links.prev;
                currentBlock->body.links.prev->body.links.next = currentBlock->body.links.next;

                currentBlock->header = (currentBlock->header & 0x7) | (currentBlock->header & ~0x7) ;
                currentBlock->header |= THIS_BLOCK_ALLOCATED;
                currentBlock->header &= ~IN_QUICK_LIST;

                if(successorBlockFetcher(currentBlock) != NULL) {
                    (successorBlockFetcher(currentBlock))->header |= PREV_BLOCK_ALLOCATED;
                    sf_footer *newFooterPtr = (sf_footer *)((char *)successorBlockFetcher(currentBlock) + ((successorBlockFetcher(currentBlock)->header) & ~0x7) - sizeof(sf_footer));
                    *newFooterPtr = (successorBlockFetcher(currentBlock))->header;
                }

                sf_block *last_block = predecessorBlockFetcher(epiloguePtr);
                if(last_block == NULL) {
                    epiloguePtr->header |= PREV_BLOCK_ALLOCATED;
                    return currentBlock->body.payload;
                }

                if ((last_block->header & 0x1) == 0x1) {
                    epiloguePtr->header |= PREV_BLOCK_ALLOCATED;
                } else {
                    epiloguePtr->header &= ~PREV_BLOCK_ALLOCATED;
                }
                return currentBlock->body.payload;
            }
            currentBlock = currentBlock->body.links.next;
        }
        loopIndex = loopIndex + 1;
    }

    sf_block *newBlock = predecessorBlockFetcher(epiloguePtr);
    if (newBlock != NULL && (newBlock->header & 0x1) == 0x1)
        newBlock = epiloguePtr;

    if(newBlock == NULL) {
        newBlock = epiloguePtr;
    }
    for(;((newBlock->header & ~0x7) < totalSize);) {
        char* memGrowAddr = sf_mem_grow();
        if (memGrowAddr == NULL) {
            sf_errno = ENOMEM;
            sf_footer *newFooterPtr = (sf_footer *)((char *)newBlock + (newBlock->header & ~0x7) - sizeof(sf_footer));
            *newFooterPtr = newBlock->header;

            epiloguePtr = (sf_block*)((char*) sf_mem_end() - 8);
            epiloguePtr->header = 0 | THIS_BLOCK_ALLOCATED;

            sf_block *last_block = predecessorBlockFetcher(epiloguePtr);
            if(last_block == NULL) {
                epiloguePtr->header |= PREV_BLOCK_ALLOCATED;
                return NULL;
            }
            if ((last_block->header & 0x1) == 0x1) {
                epiloguePtr->header |= PREV_BLOCK_ALLOCATED;
            }
            else {
                epiloguePtr->header &= ~PREV_BLOCK_ALLOCATED;
            }
            return NULL;
        }
        if (!(newBlock->body.links.next == NULL)) {
            newBlock->body.links.next->body.links.prev = newBlock->body.links.prev;
            newBlock->header = (newBlock->header & 0x7) | (newBlock->header & ~0x7);
            newBlock->body.links.prev->body.links.next = newBlock->body.links.next;
        }

        newBlock->header = (newBlock->header & 0x7) | ((newBlock->header & ~0x7) + PAGE_SZ);
        newBlock->header &= ~THIS_BLOCK_ALLOCATED;
        newBlock->header &= ~IN_QUICK_LIST;

        size_t theBlockSize = newBlock->header & ~0x7;
        size_t blockIndex = 0;
        while(theBlockSize >= 0 && blockIndex < (NUM_FREE_LISTS - 1)) {
            if (theBlockSize <= (32 * (1 << blockIndex))) {
                uintptr_t mySize = sizeof(theBlockSize);
                mySize = mySize;
                //debug("%zu", mySize);
                break;
            }
            blockIndex++;
        }
        sf_block *indexBlock = &sf_free_list_heads[blockIndex];
        size_t indexBlockSize = sizeof(indexBlock);
        sf_block *next_block = indexBlock->body.links.next;

        newBlock->body.links.next = next_block;
        indexBlockSize = sizeof(indexBlock);
        newBlock->body.links.prev = indexBlock;

        indexBlock->body.links.next = newBlock;
        indexBlockSize = sizeof(indexBlock);
        next_block->body.links.prev = newBlock;
        //debug("%zu", indexBlockSize);
        indexBlockSize = indexBlockSize;
    }

    sf_block *tempBlock = newBlock;
    newBlock->body.links.next->body.links.prev = newBlock->body.links.prev;
    newBlock->header = (newBlock->header & 0x7) | (newBlock->header & ~0x7);
    newBlock->body.links.prev->body.links.next = newBlock->body.links.next;

    if ((int) ((newBlock->header & ~0x7) - totalSize) >= 32) {
        size_t dividedSize = (newBlock->header & ~0x7) - totalSize;
        newBlock->header = (newBlock->header & 0x7) | (totalSize);
        sf_block *theNextBlockPtr = successorBlockFetcher(newBlock);

        size_t alloc_bit = (newBlock->header & 0x1);
        theNextBlockPtr->header = dividedSize;

        if(alloc_bit == 0x1) {
            theNextBlockPtr->header |= PREV_BLOCK_ALLOCATED;
        }
        else {
            theNextBlockPtr->header &= ~PREV_BLOCK_ALLOCATED;
        }

        theNextBlockPtr->header &= ~IN_QUICK_LIST;
        theNextBlockPtr->header &= ~THIS_BLOCK_ALLOCATED;

        sf_footer *newFooterPtr = (sf_footer *)((char *)theNextBlockPtr + dividedSize - sizeof(sf_footer));
        *newFooterPtr = theNextBlockPtr->header;

        tempBlock = theNextBlockPtr;

        tempBlock->header = (tempBlock->header & 0x7) | ((tempBlock->header & ~0x7));
        tempBlock->header &= ~THIS_BLOCK_ALLOCATED;
        tempBlock->header &= ~IN_QUICK_LIST;

        size_t theBlockSize = tempBlock->header & ~0x7;
        size_t blockIndex = 0;
        while(theBlockSize >= 0 && blockIndex < (NUM_FREE_LISTS - 1)) {
            if (theBlockSize <= (32 * (1 << blockIndex))) {
                uintptr_t mySize = sizeof(theBlockSize);
                mySize = mySize;
                //debug("%zu", mySize);
                break;
            }
            blockIndex++;
        }

        sf_block *indexBlock = &sf_free_list_heads[blockIndex];
        size_t indexBlockSize = sizeof(indexBlock);
        sf_block *next_block = indexBlock->body.links.next;
        indexBlockSize = sizeof(indexBlock);

        tempBlock->body.links.next = next_block;
        indexBlockSize = sizeof(indexBlock);
        tempBlock->body.links.prev = indexBlock;

        indexBlock->body.links.next = tempBlock;
        indexBlockSize = sizeof(indexBlock);
        next_block->body.links.prev = tempBlock;
        //debug("%zu", indexBlockSize);
        indexBlockSize = indexBlockSize;
    }
    epiloguePtr = (sf_block *)(((char *)sf_mem_end()) - sizeof(sf_header));

    newBlock->header = (newBlock->header & 0x7) | (newBlock->header & ~0x7);
    newBlock->header |= THIS_BLOCK_ALLOCATED;
    newBlock->header &= ~IN_QUICK_LIST;

    if(successorBlockFetcher(newBlock) != NULL) {
        (successorBlockFetcher(newBlock))->header |= PREV_BLOCK_ALLOCATED;

        sf_footer *newFooterPtr = (sf_footer *)((char *)successorBlockFetcher(newBlock) + ((successorBlockFetcher(newBlock)->header) & ~0x7) - sizeof(sf_footer));
        *newFooterPtr = (successorBlockFetcher(newBlock))->header;
    }

    epiloguePtr = (sf_block*)((char*) sf_mem_end() - 8);
    epiloguePtr->header = 0 | THIS_BLOCK_ALLOCATED;

    sf_block *last_block = predecessorBlockFetcher(epiloguePtr);
    if(last_block == NULL) {
        epiloguePtr->header |= PREV_BLOCK_ALLOCATED;
        return newBlock->body.payload;
    }

    if ((last_block->header & 0x1) == 0x1) {
        epiloguePtr->header |= PREV_BLOCK_ALLOCATED;
    } else {
        epiloguePtr->header &= ~PREV_BLOCK_ALLOCATED;
    }
    return newBlock->body.payload;
}

void sf_free(void *pp) {
    if(pp == NULL) {
        abort();
    }

    if((uintptr_t)pp % 8 != 0) {
        abort();
    }

    int numOfQuickLists = NUM_QUICK_LISTS;
    int maxQuickList = QUICK_LIST_MAX;

    sf_block* givenAllocatedBlock = (sf_block *)(((char *)pp) - 8);
    char *endGivenAllocatedBlock = (char *)givenAllocatedBlock + (givenAllocatedBlock->header & ~0x7);

    if(givenAllocatedBlock == NULL) {
        abort();
    }

    if((uintptr_t)givenAllocatedBlock % 8 != 0) {
        abort();
    }

    if ((givenAllocatedBlock->header & ~0x7) < 32) {
        abort();
    }

    if((givenAllocatedBlock->header & ~0x7) % 8 != 0) {
        abort();
    }

    if (((uintptr_t)&givenAllocatedBlock->header) >= (((uintptr_t)&epiloguePtr->header) - 8)) {
        abort();
    }

    if(((uintptr_t)&givenAllocatedBlock->header) < (((uintptr_t)&prologueStart->header) + 32)) {
        abort();
    }

    if((uintptr_t)endGivenAllocatedBlock > (((uintptr_t)&epiloguePtr->header))) {
        abort();
    }

    if ((givenAllocatedBlock->header & 0x1) == 0) {
        abort();
    }

    if ((givenAllocatedBlock->header & 0x4)) {
        abort();
    }

    if(((givenAllocatedBlock->header & 0x2) == 0 && (predecessorBlockFetcher(givenAllocatedBlock) != NULL) && !(((predecessorBlockFetcher(givenAllocatedBlock)->header) & 0x1) == 0))) {
        abort();
    }

    size_t index = ((givenAllocatedBlock->header & ~0x7) - 32) / 8;
    if (index < numOfQuickLists) {
        givenAllocatedBlock->header = (givenAllocatedBlock->header & 0x7) | (givenAllocatedBlock->header & ~0x7);
        givenAllocatedBlock->header |= THIS_BLOCK_ALLOCATED;
        givenAllocatedBlock->header |= IN_QUICK_LIST;

        if ((sf_quick_lists[index].length > maxQuickList) || (sf_quick_lists[index].length == maxQuickList)) {
            sf_block* quickListBlock = sf_quick_lists[index].first;
            for(;(!(quickListBlock == NULL));) {
                sf_block* blockHolder = quickListBlock;
                quickListBlock = quickListBlock->body.links.next;

                sf_block *successorBlock = successorBlockFetcher(blockHolder);
                sf_block *predecessorBlock = predecessorBlockFetcher(blockHolder);
                size_t origBlockSize = blockHolder->header & ~0x7;
                if (successorBlock != NULL) {
                    if((successorBlock->header & 0x1) == 0) {
                        if(!(successorBlock == epiloguePtr)) {
                            successorBlock->body.links.prev->body.links.next = successorBlock->body.links.next;
                            successorBlock->header = (successorBlock->header & 0x7) | (successorBlock->header & ~0x7);
                            successorBlock->body.links.next->body.links.prev = successorBlock->body.links.prev;
                            origBlockSize += successorBlock->header & ~0x7;
                        }
                    }
                }
                if (predecessorBlock != NULL) {
                    if((predecessorBlock->header & 0x1) == 0) {
                        if(!(predecessorBlock == prologueStart)) {
                            predecessorBlock->body.links.prev->body.links.next = predecessorBlock->body.links.next;
                            predecessorBlock->header = (predecessorBlock->header & 0x7) | (predecessorBlock->header & ~0x7);
                            predecessorBlock->body.links.next->body.links.prev = predecessorBlock->body.links.prev;
                            origBlockSize += predecessorBlock->header & ~0x7;
                            blockHolder = predecessorBlock;
                        }
                    }
                }

                blockHolder->header = (blockHolder->header & 0x7) | origBlockSize;
                blockHolder->header &= ~THIS_BLOCK_ALLOCATED;
                blockHolder->header &= ~IN_QUICK_LIST;

                if(successorBlockFetcher(blockHolder) != NULL && successorBlockFetcher(blockHolder) != epiloguePtr) {
                    (successorBlockFetcher(blockHolder))->header &= ~PREV_BLOCK_ALLOCATED;
                    int allocBit = ((successorBlockFetcher(blockHolder)->header) & 0x1);

                    if(allocBit == 0) {
                        sf_footer *newFooterPtr = (sf_footer *)((char *)successorBlockFetcher(blockHolder) + ((successorBlockFetcher(blockHolder)->header) & ~0x7) - sizeof(sf_footer));
                        *newFooterPtr = (successorBlockFetcher(blockHolder))->header;
                    }
                }

                size_t theBlockSize = blockHolder->header & ~0x7;
                size_t blockIndex = 0;

                while(theBlockSize >= 0 && blockIndex < (NUM_FREE_LISTS - 1)) {
                    if (theBlockSize <= (32 * (1 << blockIndex))) {
                        uintptr_t mySize = sizeof(theBlockSize);
                        mySize = mySize;
                        //debug("%zu", mySize);
                        break;
                    }
                    blockIndex++;
                }

                sf_block *indexBlock = &sf_free_list_heads[blockIndex];
                size_t indexBlockSize = sizeof(indexBlock);
                blockHolder->body.links.next = indexBlock->body.links.next;
                blockHolder->body.links.prev = indexBlock;
                indexBlockSize = sizeof(indexBlock);

                indexBlock->body.links.next->body.links.prev = blockHolder;
                indexBlockSize = sizeof(indexBlock);
                indexBlock->body.links.next = blockHolder;
                //debug("%zu", indexBlockSize);
                indexBlockSize = indexBlockSize;

                sf_footer *newFooterPtr = (sf_footer *)((char *)blockHolder + origBlockSize - sizeof(sf_footer));
                *newFooterPtr = blockHolder->header;
            }
            sf_quick_lists->first = NULL;
            sf_quick_lists[index].length = 0;
        }
        givenAllocatedBlock->body.links.next = sf_quick_lists[index].first;
        sf_quick_lists[index].length = sf_quick_lists[index].length + 1;
        sf_quick_lists[index].first = givenAllocatedBlock;
    }
    else {
        sf_block *successorBlock = successorBlockFetcher(givenAllocatedBlock);
        sf_block *predecessorBlock = predecessorBlockFetcher(givenAllocatedBlock);
        size_t origBlockSize = givenAllocatedBlock->header & ~0x7;
        if (successorBlock != NULL) {
            if((successorBlock->header & 0x1) == 0) {
                if(!(successorBlock == epiloguePtr)) {
                    successorBlock->body.links.prev->body.links.next = successorBlock->body.links.next;
                    successorBlock->header = (successorBlock->header & 0x7) | (successorBlock->header & ~0x7);
                    successorBlock->body.links.next->body.links.prev = successorBlock->body.links.prev;
                    origBlockSize += successorBlock->header & ~0x7;
                }
            }
        }
        if (predecessorBlock != NULL) {
            if((predecessorBlock->header & 0x1) == 0) {
                if(!(predecessorBlock == prologueStart)) {
                    predecessorBlock->body.links.prev->body.links.next = predecessorBlock->body.links.next;
                    predecessorBlock->header = (predecessorBlock->header & 0x7) | (predecessorBlock->header & ~0x7);
                    predecessorBlock->body.links.next->body.links.prev = predecessorBlock->body.links.prev;
                    origBlockSize += predecessorBlock->header & ~0x7;
                    givenAllocatedBlock = predecessorBlock;
                }
            }
        }

        givenAllocatedBlock->header = (givenAllocatedBlock->header & 0x7) | origBlockSize;
        givenAllocatedBlock->header &= ~THIS_BLOCK_ALLOCATED;
        givenAllocatedBlock->header &= ~IN_QUICK_LIST;

        if(successorBlockFetcher(givenAllocatedBlock) != NULL && successorBlockFetcher(givenAllocatedBlock) != epiloguePtr) {
            (successorBlockFetcher(givenAllocatedBlock))->header &= ~PREV_BLOCK_ALLOCATED;
            int allocBit = ((successorBlockFetcher(givenAllocatedBlock)->header) & 0x1);

            if(allocBit == 0) {
                sf_footer *newFooterPtr = (sf_footer *)((char *)successorBlockFetcher(givenAllocatedBlock) + ((successorBlockFetcher(givenAllocatedBlock)->header) & ~0x7) - sizeof(sf_footer));
                *newFooterPtr = (successorBlockFetcher(givenAllocatedBlock))->header;
            }
        }

        size_t theBlockSize = givenAllocatedBlock->header & ~0x7;
        size_t blockIndex = 0;
        while(theBlockSize >= 0 && blockIndex < (NUM_FREE_LISTS - 1)) {
            if (theBlockSize <= (32 * (1 << blockIndex))) {
                uintptr_t mySize = sizeof(theBlockSize);
                mySize = mySize;
                //debug("%zu", mySize);
                break;
            }
            blockIndex++;
        }

        sf_block *indexBlock = &sf_free_list_heads[blockIndex];
        size_t indexBlockSize = sizeof(indexBlock);

        givenAllocatedBlock->body.links.next = indexBlock->body.links.next;
        indexBlockSize = sizeof(indexBlock);
        givenAllocatedBlock->body.links.prev = indexBlock;

        indexBlock->body.links.next->body.links.prev = givenAllocatedBlock;
        indexBlockSize = sizeof(indexBlock);
        indexBlock->body.links.next = givenAllocatedBlock;
        //debug("%zu", indexBlockSize);
        indexBlockSize = indexBlockSize;

        sf_footer *newFooterPtr = (sf_footer *)((char *)givenAllocatedBlock + origBlockSize - sizeof(sf_footer));
        *newFooterPtr = givenAllocatedBlock->header;
    }

    sf_block *last_block = predecessorBlockFetcher(epiloguePtr);
    if(last_block == NULL) {
        epiloguePtr->header |= PREV_BLOCK_ALLOCATED;
        return;
    }

    if ((last_block->header & 0x1) == 0x1) {
        epiloguePtr->header |= PREV_BLOCK_ALLOCATED;
    } else {
        epiloguePtr->header &= ~PREV_BLOCK_ALLOCATED;
    }
}

void *sf_realloc(void *pp, size_t rsize) {
    if(pp == NULL) {
        sf_errno = EINVAL;
        return NULL;
    }

    if((uintptr_t)pp % 8 != 0) {
        sf_errno = EINVAL;
        return NULL;
    }

    sf_block* givenAllocatedBlock = (sf_block*)(((char *)pp) - 8);

    char *endGivenAllocatedBlock = (char *)givenAllocatedBlock + (givenAllocatedBlock->header & ~0x7);

    if(givenAllocatedBlock == NULL) {
        sf_errno = EINVAL;
        return NULL;
    }
    if((uintptr_t)givenAllocatedBlock % 8 != 0) {
        sf_errno = EINVAL;
        return NULL;
    }
    if ((givenAllocatedBlock->header & ~0x7) < 32) {
        sf_errno = EINVAL;
        return NULL;
    }
    if((givenAllocatedBlock->header & ~0x7) % 8 != 0) {
        sf_errno = EINVAL;
        return NULL;
    }
    if (((uintptr_t)&givenAllocatedBlock->header) >= (((uintptr_t)&epiloguePtr->header) - 8)) {
        sf_errno = EINVAL;
        return NULL;
    }
    if(((uintptr_t)&givenAllocatedBlock->header) < (((uintptr_t)&prologueStart->header) + 32)) {
        sf_errno = EINVAL;
        return NULL;
    }

    if((uintptr_t)endGivenAllocatedBlock > (((uintptr_t)&epiloguePtr->header))) {
        sf_errno = EINVAL;
        return NULL;
    }

    if ((givenAllocatedBlock->header & 0x1) == 0) {
        sf_errno = EINVAL;
        return NULL;
    }

    if ((givenAllocatedBlock->header & 0x4)) {
        sf_errno = EINVAL;
        return NULL;
    }

    if(((givenAllocatedBlock->header & 0x2) == 0 && (predecessorBlockFetcher(givenAllocatedBlock) != NULL) && !(((predecessorBlockFetcher(givenAllocatedBlock)->header) & 0x1) == 0))) {
        sf_errno = EINVAL;
        return NULL;
    }

    if(rsize == 0) {
        sf_free(pp);
        return NULL;
    }

    size_t originalBlockSize = (givenAllocatedBlock->header & ~0x7);

    size_t totalSize = 32;

    if(rsize <= 24) {
        totalSize = 32;
    }
    else {
        if((rsize + 8) % 8 == 0) {
            totalSize = rsize + 8;
        }
        else {
            totalSize = (rsize + 8) + (8 - ((rsize + 8) % 8));

        }
    }
    if (totalSize > originalBlockSize) {
        sf_block* mallocNewBlock = sf_malloc(rsize);
        if (mallocNewBlock == NULL) {
            sf_errno = ENOMEM;
            return NULL;
        }
        mallocNewBlock = (sf_block *)(((char *) mallocNewBlock) - 8);
        memcpy(mallocNewBlock->body.payload, givenAllocatedBlock->body.payload, originalBlockSize);
        sf_free(pp);
        return mallocNewBlock->body.payload;
    }
    else {
        if ((int) (originalBlockSize - totalSize) < 32) {
            givenAllocatedBlock->header = (givenAllocatedBlock->header & 0x7) | (originalBlockSize);
            givenAllocatedBlock->header |= THIS_BLOCK_ALLOCATED;
            givenAllocatedBlock->header &= ~IN_QUICK_LIST;

            return givenAllocatedBlock->body.payload;
        }
        else {
            size_t dividedSize = (givenAllocatedBlock->header & ~0x7) - totalSize;

            givenAllocatedBlock->header = (givenAllocatedBlock->header & 0x7) | (totalSize);
            sf_block *theNextBlockPtr = successorBlockFetcher(givenAllocatedBlock);

            size_t alloc_bit = (givenAllocatedBlock->header & 0x1);
            theNextBlockPtr->header = dividedSize;

            if(alloc_bit == 0x1) {
                theNextBlockPtr->header |= PREV_BLOCK_ALLOCATED;
            }
            else {
                theNextBlockPtr->header &= ~PREV_BLOCK_ALLOCATED;
            }

            theNextBlockPtr->header &= ~IN_QUICK_LIST;
            theNextBlockPtr->header &= ~THIS_BLOCK_ALLOCATED;

            sf_footer *newFooterPtrs = (sf_footer *)((char *)theNextBlockPtr + dividedSize - sizeof(sf_footer));
            *newFooterPtrs = theNextBlockPtr->header;

            sf_block *newAllocatedBlock = theNextBlockPtr;

            givenAllocatedBlock->header = (givenAllocatedBlock->header & 0x7) | (totalSize);
            givenAllocatedBlock->header |= THIS_BLOCK_ALLOCATED;
            givenAllocatedBlock->header &= ~IN_QUICK_LIST;

            newAllocatedBlock->header = (newAllocatedBlock->header & 0x7) | (newAllocatedBlock->header & ~0x7);
            newAllocatedBlock->header &= ~THIS_BLOCK_ALLOCATED;
            newAllocatedBlock->header &= ~IN_QUICK_LIST;

            sf_block *successorBlock = successorBlockFetcher(newAllocatedBlock);
            sf_block *predecessorBlock = predecessorBlockFetcher(newAllocatedBlock);
            size_t origBlockSize = newAllocatedBlock->header & ~0x7;
            if (successorBlock != NULL) {
                if((successorBlock->header & 0x1) == 0) {
                    if(!(successorBlock == epiloguePtr)) {
                        successorBlock->body.links.prev->body.links.next = successorBlock->body.links.next;
                        successorBlock->header = (successorBlock->header & 0x7) | (successorBlock->header & ~0x7);
                        successorBlock->body.links.next->body.links.prev = successorBlock->body.links.prev;
                        origBlockSize += successorBlock->header & ~0x7;
                    }
                }
            }

            if (predecessorBlock != NULL) {
                if((predecessorBlock->header & 0x1) == 0) {
                    if(!(predecessorBlock == prologueStart)) {
                        predecessorBlock->body.links.prev->body.links.next = predecessorBlock->body.links.next;
                        predecessorBlock->header = (predecessorBlock->header & 0x7) | (predecessorBlock->header & ~0x7);
                        predecessorBlock->body.links.next->body.links.prev = predecessorBlock->body.links.prev;
                        origBlockSize += predecessorBlock->header & ~0x7;
                        newAllocatedBlock = predecessorBlock;
                    }
                }
            }

            newAllocatedBlock->header = (newAllocatedBlock->header & 0x7) | origBlockSize;
            newAllocatedBlock->header &= ~THIS_BLOCK_ALLOCATED;
            newAllocatedBlock->header &= ~IN_QUICK_LIST;

            if(successorBlockFetcher(newAllocatedBlock) != NULL && successorBlockFetcher(newAllocatedBlock) != epiloguePtr) {
                (successorBlockFetcher(newAllocatedBlock))->header &= ~PREV_BLOCK_ALLOCATED;
                int allocBit = ((successorBlockFetcher(newAllocatedBlock)->header) & 0x1);

                if(allocBit == 0) {
                    sf_footer *newFooterPtr = (sf_footer *)((char *)successorBlockFetcher(newAllocatedBlock) + ((successorBlockFetcher(newAllocatedBlock)->header) & ~0x7) - sizeof(sf_footer));
                    *newFooterPtr = (successorBlockFetcher(newAllocatedBlock))->header;
                }
            }

            size_t theBlockSize = newAllocatedBlock->header & ~0x7;
            size_t blockIndex = 0;
            while(theBlockSize >= 0 && blockIndex < (NUM_FREE_LISTS - 1)) {
                if (theBlockSize <= (32 * (1 << blockIndex))) {
                    uintptr_t mySize = sizeof(theBlockSize);
                    mySize = mySize;
                    //debug("%zu", mySize);
                    break;
                }
                blockIndex++;
            }

            sf_block *indexBlock = &sf_free_list_heads[blockIndex];
            size_t indexBlockSize = sizeof(indexBlock);

            newAllocatedBlock->body.links.next = indexBlock->body.links.next;
            indexBlockSize = sizeof(indexBlock);
            newAllocatedBlock->body.links.prev = indexBlock;

            indexBlock->body.links.next->body.links.prev = newAllocatedBlock;
            indexBlockSize = sizeof(indexBlock);
            indexBlock->body.links.next = newAllocatedBlock;
            //debug("%zu", indexBlockSize);
            indexBlockSize = indexBlockSize;

            sf_footer *newFooterPtr = (sf_footer *)((char *)newAllocatedBlock + origBlockSize - sizeof(sf_footer));
            *newFooterPtr = newAllocatedBlock->header;

            return givenAllocatedBlock->body.payload;
        }
    }
}

void *sf_memalign(size_t size, size_t align) {
    if(size == 0) {
        return NULL;
    }

    if(align < 8) {
        sf_errno = EINVAL;
        return NULL;
    }

    if(!((align != 0) && ((align & (align - 1)) == 0))) {
        sf_errno = EINVAL;
        return NULL;
    }

    char* mallocNewBlock = sf_malloc(32 + align + size);

    if(sf_errno == ENOMEM && mallocNewBlock == NULL) {
        return NULL;
    }

    char* memalignedBlock = mallocNewBlock;

    if(memalignedBlock != NULL && (uintptr_t)mallocNewBlock % align == 0) {
        return sf_realloc(mallocNewBlock, size);
    }

    sf_block* newBlock = (sf_block*)(mallocNewBlock - sizeof(sf_header));
    int loopCounter = 0;
    uint64_t originalSize = (newBlock->header & ~0x7);

    while(loopCounter < originalSize && originalSize != 0) {
        memalignedBlock++;
        if(memalignedBlock != NULL && (uintptr_t)memalignedBlock % align == 0 && (uintptr_t)(memalignedBlock - (char*)newBlock) - sizeof(sf_header) >= 32) {
            break;
        }
        loopCounter++;
    }

    uint64_t allocBlockSize = (memalignedBlock - 8) - (char *)newBlock;

    newBlock->header = (newBlock->header & 0x7) | allocBlockSize;
    newBlock->header |= THIS_BLOCK_ALLOCATED;

    uint64_t newBlockSize = originalSize - allocBlockSize;

    size_t totalSize = 32;

    if(size <= 24) {
        totalSize = 32;
    }
    else {
        if((size + 8) % 8 == 0) {
            totalSize = size + 8;
        }
        else {
            totalSize = (size + 8) + (8 - ((size + 8) % 8));
        }
    }

    size_t sizeDifference = newBlockSize - totalSize;

    if((int)(sizeDifference) < 32) {
        sf_block* tempBlock = (sf_block*)(memalignedBlock - sizeof(sf_header));
        tempBlock->header = (tempBlock->header & 0x7) | newBlockSize;
        tempBlock->header |= THIS_BLOCK_ALLOCATED;
        tempBlock->header |= PREV_BLOCK_ALLOCATED;

        sf_block *block1 = (sf_block *)(((uintptr_t)mallocNewBlock) - sizeof(sf_header));

        if((block1->header & ~0x7) >= 32) {
            sf_block *successorBlock = successorBlockFetcher(block1);
            sf_block *predecessorBlock = predecessorBlockFetcher(block1);
            size_t origBlockSize = block1->header & ~0x7;
            if (successorBlock != NULL) {
                if((successorBlock->header & 0x1) == 0) {
                    if(!(successorBlock == epiloguePtr)) {
                        successorBlock->body.links.prev->body.links.next = successorBlock->body.links.next;
                        successorBlock->header = (successorBlock->header & 0x7) | (successorBlock->header & ~0x7);
                        successorBlock->body.links.next->body.links.prev = successorBlock->body.links.prev;
                        origBlockSize += successorBlock->header & ~0x7;
                    }
                }
            }

            if (predecessorBlock != NULL) {
                if((predecessorBlock->header & 0x1) == 0) {
                    if(!(predecessorBlock == prologueStart)) {
                        predecessorBlock->body.links.prev->body.links.next = predecessorBlock->body.links.next;
                        predecessorBlock->header = (predecessorBlock->header & 0x7) | (predecessorBlock->header & ~0x7);
                        predecessorBlock->body.links.next->body.links.prev = predecessorBlock->body.links.prev;
                        origBlockSize += predecessorBlock->header & ~0x7;
                        block1 = predecessorBlock;
                    }
                }
            }

            block1->header = (block1->header & 0x7) | origBlockSize;
            block1->header &= ~THIS_BLOCK_ALLOCATED;
            block1->header &= ~IN_QUICK_LIST;

            if(successorBlockFetcher(block1) != NULL && successorBlockFetcher(block1) != epiloguePtr) {
                (successorBlockFetcher(block1))->header &= ~PREV_BLOCK_ALLOCATED;
                int allocBit = ((successorBlockFetcher(block1)->header) & 0x1);

                if(allocBit == 0) {
                    sf_footer *newFooterPtr = (sf_footer *)((char *)successorBlockFetcher(block1) + ((successorBlockFetcher(block1)->header) & ~0x7) - sizeof(sf_footer));
                    *newFooterPtr = (successorBlockFetcher(block1))->header;
                }
            }

            size_t theBlockSize = block1->header & ~0x7;
            size_t blockIndex = 0;
            while(theBlockSize >= 0 && blockIndex < (NUM_FREE_LISTS - 1)) {
                if (theBlockSize <= (32 * (1 << blockIndex))) {
                    uintptr_t mySize = sizeof(theBlockSize);
                    mySize = mySize;
                    //debug("%zu", mySize);
                    break;
                }
                blockIndex++;
            }

            sf_block *indexBlock = &sf_free_list_heads[blockIndex];
            size_t indexBlockSize = sizeof(indexBlock);

            block1->body.links.next = indexBlock->body.links.next;
            indexBlockSize = sizeof(indexBlock);
            block1->body.links.prev = indexBlock;

            indexBlock->body.links.next->body.links.prev = block1;
            indexBlockSize = sizeof(indexBlock);
            indexBlock->body.links.next = block1;
            //debug("%zu", indexBlockSize);
            indexBlockSize = indexBlockSize;

            sf_footer *newFooterPtr = (sf_footer *)((char *)block1 + origBlockSize - sizeof(sf_footer));
            *newFooterPtr = block1->header;
        }
        return memalignedBlock;
    }

    else {
        sf_block* tempBlock = (sf_block*)(memalignedBlock - sizeof(sf_header));
        tempBlock->header = (tempBlock->header & 0x7) | totalSize;
        tempBlock->header |= THIS_BLOCK_ALLOCATED;
        tempBlock->header |= PREV_BLOCK_ALLOCATED;

        sf_block* memSuccessorBlock = (sf_block*)(memalignedBlock + totalSize - sizeof(sf_header));
        memSuccessorBlock->header = (memSuccessorBlock->header & 0x7) | (newBlockSize - totalSize);
        memSuccessorBlock->header |= THIS_BLOCK_ALLOCATED;
        memSuccessorBlock->header |= PREV_BLOCK_ALLOCATED;

        sf_block* block1 = (sf_block*)(((uintptr_t)mallocNewBlock) - sizeof(sf_header));

        if((block1->header & ~0x7) >= 32) {
            sf_block *successorBlock = successorBlockFetcher(block1);
            sf_block *predecessorBlock = predecessorBlockFetcher(block1);
            size_t origBlockSize = block1->header & ~0x7;
            if (successorBlock != NULL) {
                if((successorBlock->header & 0x1) == 0) {
                    if(!(successorBlock == epiloguePtr)) {
                        successorBlock->body.links.prev->body.links.next = successorBlock->body.links.next;
                        successorBlock->header = (successorBlock->header & 0x7) | (successorBlock->header & ~0x7);
                        successorBlock->body.links.next->body.links.prev = successorBlock->body.links.prev;
                        origBlockSize += successorBlock->header & ~0x7;
                    }
                }
            }

            if (predecessorBlock != NULL) {
                if((predecessorBlock->header & 0x1) == 0) {
                    if(!(predecessorBlock == prologueStart)) {
                        predecessorBlock->body.links.prev->body.links.next = predecessorBlock->body.links.next;
                        predecessorBlock->header = (predecessorBlock->header & 0x7) | (predecessorBlock->header & ~0x7);
                        predecessorBlock->body.links.next->body.links.prev = predecessorBlock->body.links.prev;
                        origBlockSize += predecessorBlock->header & ~0x7;
                        block1 = predecessorBlock;
                    }
                }
            }

            block1->header = (block1->header & 0x7) | origBlockSize;
            block1->header &= ~THIS_BLOCK_ALLOCATED;
            block1->header &= ~IN_QUICK_LIST;

            if(successorBlockFetcher(block1) != NULL && successorBlockFetcher(block1) != epiloguePtr) {
                (successorBlockFetcher(block1))->header &= ~PREV_BLOCK_ALLOCATED;
                int allocBit = ((successorBlockFetcher(block1)->header) & 0x1);

                if(allocBit == 0) {
                    sf_footer *newFooterPtr = (sf_footer *)((char *)successorBlockFetcher(block1) + ((successorBlockFetcher(block1)->header) & ~0x7) - sizeof(sf_footer));
                    *newFooterPtr = (successorBlockFetcher(block1))->header;
                }
            }

            size_t theBlockSize = block1->header & ~0x7;
            size_t blockIndex = 0;
            while(theBlockSize >= 0 && blockIndex < (NUM_FREE_LISTS - 1)) {
                if (theBlockSize <= (32 * (1 << blockIndex))) {
                    uintptr_t mySize = sizeof(theBlockSize);
                    mySize = mySize;
                    //debug("%zu", mySize);
                    break;
                }
                blockIndex++;
            }

            sf_block *indexBlock = &sf_free_list_heads[blockIndex];
            size_t indexBlockSize = sizeof(indexBlock);

            block1->body.links.next = indexBlock->body.links.next;
            indexBlockSize = sizeof(indexBlock);
            block1->body.links.prev = indexBlock;

            indexBlock->body.links.next->body.links.prev = block1;
            indexBlockSize = sizeof(indexBlock);
            indexBlock->body.links.next = block1;
            //debug("%zu", indexBlockSize);
            indexBlockSize = indexBlockSize;

            sf_footer *newFooterPtr = (sf_footer *)((char *)block1 + origBlockSize - sizeof(sf_footer));
            *newFooterPtr = block1->header;
        }

        if((memSuccessorBlock->header & ~0x7) >= 32) {
            sf_block *successorBlock = successorBlockFetcher(memSuccessorBlock);
            sf_block *predecessorBlock = predecessorBlockFetcher(memSuccessorBlock);
            size_t origBlockSize = memSuccessorBlock->header & ~0x7;
            if (successorBlock != NULL) {
                if((successorBlock->header & 0x1) == 0) {
                    if(!(successorBlock == epiloguePtr)) {
                        successorBlock->body.links.prev->body.links.next = successorBlock->body.links.next;
                        successorBlock->header = (successorBlock->header & 0x7) | (successorBlock->header & ~0x7);
                        successorBlock->body.links.next->body.links.prev = successorBlock->body.links.prev;
                        origBlockSize += successorBlock->header & ~0x7;
                    }
                }
            }

            if (predecessorBlock != NULL) {
                if((predecessorBlock->header & 0x1) == 0) {
                    if(!(predecessorBlock == prologueStart)) {
                        predecessorBlock->body.links.prev->body.links.next = predecessorBlock->body.links.next;
                        predecessorBlock->header = (predecessorBlock->header & 0x7) | (predecessorBlock->header & ~0x7);
                        predecessorBlock->body.links.next->body.links.prev = predecessorBlock->body.links.prev;
                        origBlockSize += predecessorBlock->header & ~0x7;
                        memSuccessorBlock = predecessorBlock;
                    }
                }
            }

            memSuccessorBlock->header = (memSuccessorBlock->header & 0x7) | origBlockSize;
            memSuccessorBlock->header &= ~THIS_BLOCK_ALLOCATED;
            memSuccessorBlock->header &= ~IN_QUICK_LIST;

            if(successorBlockFetcher(memSuccessorBlock) != NULL && successorBlockFetcher(memSuccessorBlock) != epiloguePtr) {
                (successorBlockFetcher(memSuccessorBlock))->header &= ~PREV_BLOCK_ALLOCATED;
                int allocBit = ((successorBlockFetcher(memSuccessorBlock)->header) & 0x1);

                if(allocBit == 0) {
                    sf_footer *newFooterPtr = (sf_footer *)((char *)successorBlockFetcher(memSuccessorBlock) + ((successorBlockFetcher(memSuccessorBlock)->header) & ~0x7) - sizeof(sf_footer));
                    *newFooterPtr = (successorBlockFetcher(memSuccessorBlock))->header;
                }
            }

            size_t theBlockSize = memSuccessorBlock->header & ~0x7;
            size_t blockIndex = 0;
            while(theBlockSize >= 0 && blockIndex < (NUM_FREE_LISTS - 1)) {
                if (theBlockSize <= (32 * (1 << blockIndex))) {
                    uintptr_t mySize = sizeof(theBlockSize);
                    mySize = mySize;
                    //debug("%zu", mySize);
                    break;
                }
                blockIndex++;
            }

            sf_block *indexBlock = &sf_free_list_heads[blockIndex];
            size_t indexBlockSize = sizeof(indexBlock);

            memSuccessorBlock->body.links.next = indexBlock->body.links.next;
            indexBlockSize = sizeof(indexBlock);
            memSuccessorBlock->body.links.prev = indexBlock;

            indexBlock->body.links.next->body.links.prev = memSuccessorBlock;
            indexBlockSize = sizeof(indexBlock);
            indexBlock->body.links.next = memSuccessorBlock;
            //debug("%zu", indexBlockSize);
            indexBlockSize = indexBlockSize;

            sf_footer *newFooterPtr = (sf_footer *)((char *)memSuccessorBlock + origBlockSize - sizeof(sf_footer));
            *newFooterPtr = memSuccessorBlock->header;
        }
        return memalignedBlock;
    }
}
