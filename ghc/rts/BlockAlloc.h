/* -----------------------------------------------------------------------------
 * $Id: BlockAlloc.h,v 1.7 1999/11/02 17:08:28 simonmar Exp $
 *
 * (c) The GHC Team, 1998-1999
 *
 * Block Allocator Interface
 *
 * ---------------------------------------------------------------------------*/

#ifndef BLOCK_ALLOC_H
#define BLOCK_ALLOC_H

/* Initialisation ---------------------------------------------------------- */

extern void initBlockAllocator(void);

/* Allocation -------------------------------------------------------------- */

extern bdescr *allocGroup(nat n);
extern bdescr *allocBlock(void);

/* De-Allocation ----------------------------------------------------------- */

extern void freeGroup(bdescr *p);
extern void freeChain(bdescr *p);

/* Finding the block descriptor for a given block -------------------------- */

static inline bdescr *Bdescr(StgPtr p)
{
  return (bdescr *)
    ((((W_)p &  MBLOCK_MASK & ~BLOCK_MASK) >> (BLOCK_SHIFT-BDESCR_SHIFT)) 
     | ((W_)p & ~MBLOCK_MASK)
     );
}

/* Round a value to megablocks --------------------------------------------- */

#define WORDS_PER_MBLOCK  (BLOCKS_PER_MBLOCK * BLOCK_SIZE_W)

static inline nat
round_to_mblocks(nat words)
{
  if (words > WORDS_PER_MBLOCK) {
    if ((words % WORDS_PER_MBLOCK) < (WORDS_PER_MBLOCK / 2)) {
      words = (words / WORDS_PER_MBLOCK) * WORDS_PER_MBLOCK;
    } else {
      words = ((words / WORDS_PER_MBLOCK) + 1) * WORDS_PER_MBLOCK;
    }
  }
  return words;
}

/* Debugging  -------------------------------------------------------------- */

#ifdef DEBUG
extern void checkFreeListSanity(void);
nat         countFreeList(void);
#endif

#endif BLOCK_ALLOC_H
