/* Configuration for the mruby-bignum gem */

#ifndef MRB_BIGNUM_CONF_H
#define MRB_BIGNUM_CONF_H

/* Size of a Bignum digit:  16, 32 or 64 */
/* If not defined, this is the same size as a Fixnum */
/* To use MRB_BIGNUM_BIT == 64, the compiler must support unsigned __int128 */
#define MRB_BIGNUM_BIT 64

/* Define to enable recursive algorithms for multiplication, division,
   squaring, and conversion to and from strings */
#define MRB_BIGNUM_ENABLE_RECURSION

/* Cutoffs for recursive multiplication, squaring and division */
#define MRB_BIGNUM_MUL_RECURSION_CUTOFF 32
#define MRB_BIGNUM_SQR_RECURSION_CUTOFF 64
#define MRB_BIGNUM_DIV_RECURSION_CUTOFF 32

#endif
