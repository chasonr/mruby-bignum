/* bignum-gem.c */

#include <mruby.h>
#include <mruby/array.h>
#include <mruby/class.h>
#include <mruby/data.h>
#include <mruby/numeric.h>
#include <mruby/string.h>
#include <ctype.h>
#include <math.h>
#include <stddef.h>
#include <string.h>
#include "bignum-conf.h"

/* MRB_BIGNUM_BIT defaults to the same size as a Fixnum */
#ifndef MRB_BIGNUM_BIT
# define MRB_BIGNUM_BIT MRB_INT_BIT
#endif /* MRB_BIGNUM_BIT */

/* Set the bignum digit types */
#if MRB_BIGNUM_BIT == 16
  typedef uint16_t bn_digit;
  typedef uint32_t bn_dbl_digit;
#elif MRB_BIGNUM_BIT == 32
  typedef uint32_t bn_digit;
  typedef uint64_t bn_dbl_digit;
#elif MRB_BIGNUM_BIT == 64
  typedef uint64_t bn_digit;
  typedef unsigned __int128 bn_dbl_digit;
#else
# error "MRB_BIGNUM_BIT must be 16, 32 or 64"
#endif

/* For the math functions */
#ifdef MRB_USE_FLOAT
# define F(x) x##f
#else
# define F(x) x
#endif

/* For converting Fixnum to Bignum */
#if MRB_INT_BIT == 16
  typedef uint16_t mrb_uint;
#elif MRB_INT_BIT == 32
  typedef uint32_t mrb_uint;
#else
  typedef uint64_t mrb_uint;
#endif

/* Number of bignum digits needed to represent a Fixnum */
#define FIXNUM_DIGITS ((MRB_INT_BIT+MRB_BIGNUM_BIT-1)/MRB_BIGNUM_BIT)

/* Enable default conversion to Fixnum if this is true */
#ifdef MRB_BIGNUM_INTEGRATION
#define FIXNUM_CONVERT TRUE
#else
#define FIXNUM_CONVERT FALSE
#endif

struct Bignum {
  size_t len;
  mrb_bool negative;
  bn_digit digits[1];
};

/* Allocate a Bignum with the given number of digits */
static struct Bignum *
bn_alloc(mrb_state *mrb, size_t len)
{
  struct Bignum *num;
  size_t size;

  /* Compute allocation size and detect overflow */
  size = len * sizeof(bn_digit);
  if (size / sizeof(bn_digit) != len) {
    goto overflow;
  }
  size += offsetof(struct Bignum, digits);
  if (size < offsetof(struct Bignum, digits)) {
    goto overflow;
  }

  /* Allocate and fill the structure */
  num = (struct Bignum *)mrb_malloc(mrb, size);
  memset(num, 0, size);
  num->len = len;
  num->negative = FALSE;

  return num;

overflow:
  mrb_raise(mrb, E_RUNTIME_ERROR, "Bignum allocation too large");
  return NULL;
}

/* Free memory belonging to a Bignum */
static void
bn_free(mrb_state *mrb, void *num)
{
  mrb_free(mrb, num);
}

/* Data type structure for the class */
static struct mrb_data_type bignum_type = {
  "Bignum", bn_free
};

/* ------------------------------------------------------------------------*/

/* Ensure only one representation of a Bignum */
static struct Bignum *
bn_normalize(struct Bignum *num)
{
  /* Minimize num->len */
  while (num->len != 0 && num->digits[num->len-1] == 0) {
    --num->len;
  }
  /* Only one representation of zero */
  if (num->len == 0) {
    num->negative = FALSE;
  }
  return num;
}

/* Identify the object as a numeric type */
enum num_type {
  num_none,
  num_fixnum,
  num_bignum,
  num_float
};

static enum num_type
num_identify(mrb_state *mrb, mrb_value obj)
{
  switch (mrb_type(obj)) {
  case MRB_TT_FIXNUM:
    return num_fixnum;
  case MRB_TT_FLOAT:
    return num_float;
  case MRB_TT_DATA:
    return DATA_TYPE(obj) == &bignum_type ? num_bignum : num_none;
  default:
    return num_none;
  }
}

/* Convert a Fixnum to a Bignum */
static struct Bignum *
fixnum_to_bignum(mrb_state *mrb, mrb_int num)
{
  mrb_uint unum;
  struct Bignum *bignum;

  bignum = bn_alloc(mrb, FIXNUM_DIGITS);
  bignum->negative = num < 0;
  unum = (num < 0) ? -(mrb_uint)num : +(mrb_uint)num;
#if FIXNUM_DIGITS == 1
  /* avoid undefined behavior in the shift */
  bignum->digits[0] = unum;
  bignum->len = (unum == 0) ? 0 : 1;
#else
  {
    unsigned i;
    for (i = 0; i < FIXNUM_DIGITS && unum != 0; ++i) {
      bignum->digits[i] = (bn_digit)unum;
      unum >>= MRB_BIGNUM_BIT;
    }
    bignum->len = i;
  }
#endif
  return bignum;
}

/* Convert a floating point number to a Bignum */
static struct Bignum *
float_to_bignum(mrb_state *mrb, mrb_float num)
{
  mrb_float unum;
  int exponent, offset;
  size_t i;
  struct Bignum *bignum;

  /* Split into significand and exponent */
  unum = F(frexp)(F(fabs)(num), &exponent);

  /* Allocate the Bignum */
  bignum = bn_alloc(mrb, (exponent + MRB_BIGNUM_BIT - 1) / MRB_BIGNUM_BIT);
  bignum->negative = num < 0;

  /* Shift unum so that, when multiplied by 2**MRB_BIGNUM_BIT, the integer
     part will be the top digit of the Bignum */
  offset = bignum->len * MRB_BIGNUM_BIT - exponent;
  unum = F(ldexp)(unum, -offset);

  /* On each pass, convert one digit of the Bignum */
  for (i = bignum->len; i-- != 0 && unum != 0; ) {
    mrb_float digit;
    unum = F(ldexp)(unum, MRB_BIGNUM_BIT);
    unum = F(modf)(unum, &digit);
    bignum->digits[i] = (bn_digit)digit;
  }

  return bn_normalize(bignum);
}

/* Convert a Bignum to a Fixnum; return nil if not possible */
static mrb_value
bignum_to_fixnum(struct Bignum *num)
{
#if FIXNUM_DIGITS == 1 /* bn_digit may be larger than mrb_uint */
  bn_digit ufix;
#else
  mrb_uint ufix;
#endif
  mrb_bool overflow = num->len > FIXNUM_DIGITS;

  if (!overflow) {
#if FIXNUM_DIGITS == 1
    ufix = (num->len == 0) ? 0 : num->digits[0];
#else
    /* Assumes MRB_INT_BIT is a multiple of MRB_BIGNUM_BIT */
    size_t i;
    ufix = 0;
    for (i = num->len; i-- != 0; ) {
      ufix = (ufix << MRB_BIGNUM_BIT) | num->digits[i];
    }
#endif
    overflow = ( num->negative && ufix > (mrb_uint)MRB_INT_MAX+1)
            || (!num->negative && ufix > (mrb_uint)MRB_INT_MAX+0);
  }
  if (!overflow) {
    return mrb_fixnum_value((mrb_int)(num->negative ? -ufix : +ufix));
  }
  else {
    return mrb_nil_value();
  }
}

/* Convert a Bignum to int64_t; return INT64_MIN if not possible */
/* For the <<, >> and ** operators when the right side is a Bignum */
static int64_t
bignum_to_int64(struct Bignum const *num)
{
  uint64_t ufix;
  mrb_bool overflow = num->len > 64 / MRB_BIGNUM_BIT;

  if (!overflow) {
#if MRB_BIGNUM_BIT == 64
    ufix = (num->len == 0) ? 0 : num->digits[0];
#else
    size_t i;
    ufix = 0;
    for (i = num->len; i-- != 0; ) {
      ufix = (ufix << MRB_BIGNUM_BIT) | num->digits[i];
    }
#endif

    overflow = ufix > INT64_MAX;
  }
  if (!overflow) {
    return (int64_t)(num->negative ? -ufix : +ufix);
  }
  else {
    return INT64_MIN;
  }
}

/* Create a new Bignum or Fixnum as a Ruby object */
/* Takes custody of the struct Bignum object; it is under the control of the
   Ruby object if the object is a Bignum, and freed if converted to a Fixnum */
static mrb_value
new_bignum(mrb_state *mrb, struct Bignum *num, mrb_bool fixnum_conv)
{
  /* Can we return a Fixnum? */
  if (fixnum_conv) {
    mrb_value fix = bignum_to_fixnum(num);
    if (mrb_fixnum_p(fix)) {
      /* Return a Fixnum */
      bn_free(mrb, num);
      return fix;
    }
  }

  /* Return a Bignum */
  return mrb_obj_value(mrb_data_object_alloc(mrb,
        mrb_class_get(mrb, "Bignum"), num, &bignum_type));
}

/* Convert a Bignum to a Float */
static mrb_float
bn_to_float(struct Bignum const *num)
{
  uint64_t significand, top_bit;
  int exponent;
  unsigned bits;
  size_t i;
  mrb_float f;

  /* Ensure the conversion has something to work with */
  if (num->len == 0) {
    return 0;
  }
  /* Avoid overflow in the exponent */
  if (num->len > INT_MAX/MRB_BIGNUM_BIT) {
    return num->negative ? -INFINITY : +INFINITY;
  }

  /* This will round correctly as long as the floating point type has no more
     than 62 significant bits */

  /* Get the top 64 bits */
  exponent = num->len * MRB_BIGNUM_BIT - 64;
  i = num->len;
  significand = num->digits[--i];
  bits = MRB_BIGNUM_BIT;
  top_bit = (uint64_t)1 << (MRB_BIGNUM_BIT - 1);
  while ((significand & top_bit) == 0) {
    top_bit >>= 1;
    --bits;
    --exponent;
  }
#if MRB_BIGNUM_BIT < 64
  while (i != 0 && bits + MRB_BIGNUM_BIT <= 64) {
    significand = (significand << MRB_BIGNUM_BIT) | num->digits[--i];
    bits += MRB_BIGNUM_BIT;
  }
#endif

  /* bits is how many bits we have in significand */
  /* If i == 0, there are no more bits to gather; otherwise, we can possibly
     get more bits from the next digit */
  if (i != 0 && bits < 64) {
    unsigned lshift = 64 - bits;
    unsigned rshift = MRB_BIGNUM_BIT - lshift;
    significand = (significand << lshift) | (num->digits[--i] >> rshift);
    bits = 64;
    if ((num->digits[i] & (((bn_digit)1 << lshift) - 1U)) != 0) {
      /* Account for the rest of num->digits[i], for rounding */
      significand |= 1;
    }
  }

  if (i == 0) {
    significand <<= 64 - bits;
  }
  else {
    /* Account for remaining digits, for rounding */
    while ((significand & 1) == 0 && i != 0) {
      if (num->digits[--i] != 0) {
        significand |= 1;
      }
    }
  }

  /* Convert to float and include the sign */
  f = (mrb_float)significand;
  if (num->negative) {
    f = -f;
  }
  return F(ldexp)(f, exponent);
}

/* Compare absolute values of in1 and in2 */
/* Return -1, 0 or +1 */
static int
bn_cmp_basic(
        bn_digit const *in1, size_t in1_size,
        bn_digit const *in2, size_t in2_size)
{
  size_t i;

  if (in1_size < in2_size) {
    return -1;
  }
  if (in1_size > in2_size) {
    return +1;
  }

  for (i = in1_size; i-- != 0; ) {
    if (in1[i] < in2[i]) {
      return -1;
    }
    if (in1[i] > in2[i]) {
      return +1;
    }
  }

  return 0;
}

/* Compare absolute values of in1 and in2 */
/* Return -1, 0 or +1 */
static int
bn_cmp_unsigned(struct Bignum const *in1, struct Bignum const *in2)
{
  return bn_cmp_basic(in1->digits, in1->len, in2->digits, in2->len);
}

/* Compare in1 and in2 as signed quantities */
/* Return -1, 0 or +1 */
static int
bn_cmp(struct Bignum const *in1, struct Bignum const *in2)
{
  int cmp;

  if (in1->negative && !in2->negative) {
    return -1;
  }
  if (in2->negative && !in1->negative) {
    return +1;
  }

  cmp = bn_cmp_unsigned(in1, in2);
  if (in1->negative) {
    cmp = -cmp;
  }

  return cmp;
}

/* Add unsigned quantities, and return carry (0 or 1) */
/* out may be the same as in1 */
static unsigned
bn_add_basic(
        bn_digit *out, /* Size is max(in1_size, in2_size) */
        const bn_digit *in1, size_t in1_size,
        const bn_digit *in2, size_t in2_size)
{
  unsigned carry;
  size_t i;

  /* Make in1 the longer input */
  if (in1_size < in2_size) {
    const bn_digit *s;
    size_t s_size;
    s = in1;
    in1 = in2;
    in2 = s;
    s_size = in1_size;
    in1_size = in2_size;
    in2_size = s_size;
  }

  /* Add to the size of in2 */
  carry = 0U;
  for (i = 0U; i < in2_size; ++i) {
    bn_digit sum = in1[i] + in2[i] + carry;
    if (sum < in1[i]) { carry = 1U; }
    if (sum > in1[i]) { carry = 0U; }
    out[i] = sum;
  }

  /* Continue to the size of in1: */
  /* with carry */
  for (; i < in1_size && carry; ++i) {
    out[i] = in1[i] + 1U;
    if (out[i] != 0U) { carry = 0U; }
  }
  /* without carry */
  for (; i < in1_size; ++i) {
    out[i] = in1[i];
  }

  return carry;
}

/* Add absolute values, and return a new struct Bignum */
static struct Bignum *
bn_add_unsigned(mrb_state *mrb, struct Bignum const *in1, struct Bignum const *in2)
{
  struct Bignum *out;

  /* Make in1 the longer input */
  if (in1->len < in2->len) {
    struct Bignum const *swp;
    swp = in1;
    in1 = in2;
    in2 = swp;
  }

  /* Allocate output */
  out = bn_alloc(mrb, in1->len + 1);

  out->digits[in1->len] = bn_add_basic(out->digits,
          in1->digits, in1->len, in2->digits, in2->len);

  return bn_normalize(out);
}

/* Subtract unsigned quantities; assume that in1 >= in2 */
/* out may be the same as in1 */
void
bn_sub_basic(
        bn_digit *out, /* Size is in1_size */
        const bn_digit *in1, size_t in1_size,
        const bn_digit *in2, size_t in2_size)
{
  unsigned borrow;
  size_t i;

  /* Remove leading zeros from in2 */
  while (in2_size != 0U && in2[in2_size-1U] == 0U) { --in2_size; }

  /* Subtract to the size of in2 */
  borrow = 0U;
  for (i = 0U; i < in2_size; ++i) {
    bn_digit diff = in1[i] - in2[i] - borrow;
    if (diff < in1[i]) { borrow = 0U; }
    if (diff > in1[i]) { borrow = 1U; }
    out[i] = diff;
  }

  /* Continue to the size of in1: */
  /* with borrow */
  for (; i < in1_size && borrow; ++i) {
    if (in1[i] != 0U) { borrow = 0U; }
    out[i] = in1[i] - 1U;
  }
  /* without borrow */
  for (; i < in1_size; ++i) {
    out[i] = in1[i];
  }
}

/* Subtract absolute values, and return a new struct Bignum */
/* Caller must ensure that in1 >= in2 */
static struct Bignum *
bn_sub_unsigned(mrb_state *mrb, struct Bignum const *in1, struct Bignum const *in2)
{
  struct Bignum *out;

  out = bn_alloc(mrb, in1->len);

  bn_sub_basic(out->digits, in1->digits, in1->len, in2->digits, in2->len);

  return bn_normalize(out);
}

/* Add or subtract in1 and in2 as signed quantities, and return a new
   struct Bignum */
static struct Bignum *
bn_add(mrb_state *mrb, struct Bignum const *in1, struct Bignum const *in2, mrb_bool subtract)
{
  struct Bignum *sum;
  mrb_bool sign1 = in1->negative != 0;
  mrb_bool sign2 = (in2->negative != 0) ^ (subtract != 0);

  if (sign1 == sign2) {
    /* Add */
    sum = bn_add_unsigned(mrb, in1, in2);
    sum->negative = sign1;
  }
  else {
    /* Subtract */
    if (bn_cmp_unsigned(in1, in2) >= 0) {
      sum = bn_sub_unsigned(mrb, in1, in2);
      sum->negative = sign1;
    }
    else {
      sum = bn_sub_unsigned(mrb, in2, in1);
      sum->negative = sign2;
    }
  }

  return bn_normalize(sum);
}

/* Multiply:  basic algorithm */
static void
bn_mul_basic(
        bn_digit *out, /* Size is in1_size + in2_size */
        const bn_digit *in1, size_t in1_size,
        const bn_digit *in2, size_t in2_size)
{
  size_t out_size = in1_size + in2_size;

  /* Remove leading zeros */
  while (in1_size != 0U && in1[in1_size-1U] == 0U) {
    out[--out_size] = 0U;
    --in1_size;
  }
  while (in2_size != 0U && in2[in2_size-1U] == 0U) {
    out[--out_size] = 0U;
    --in2_size;
  }

  /* Set up the product for the main loop */
  for (size_t j = 0U; j < in2_size; ++j) {
    out[j] = 0U;
  }

  /* Invariant for the outer loop:  out has i+in2_size digits and contains the
     product of the first i digits of in1 with all of in2 */
  for (size_t i = 0U; i < in1_size; ++i) {
    /* Inner loop:  multiply one digit of in1 by in2 and add to prod */
    bn_digit carry = 0U;
    for (size_t j = 0U; j < in2_size; ++j) {
      /* Never overflows, because */
      /* (2^N-1)*(2^N-1) + (2^N-1) + (2^N-1) = 2^(2*N)-1 */
      bn_dbl_digit prod = (bn_dbl_digit)in1[i] * in2[j] + carry + out[i+j];
      out[i+j] = (bn_digit)prod;
      carry = (bn_digit)(prod >> MRB_BIGNUM_BIT);
    }
    out[i+in2_size] = carry;
  }
}

#ifdef MRB_BIGNUM_ENABLE_RECURSION
static void
bn_mul_recursive(
        mrb_state *mrb,
        bn_digit *out, /* Size is in1_size + in2_size */
        const bn_digit *in1, size_t in1_size,
        const bn_digit *in2, size_t in2_size);

/* "Single digit" multiply, where the "digit" has the size of in2 */
/* Use when in1_size >= in2_size*2 */
static void
bn_mul_lopsided(
        mrb_state *mrb,
        bn_digit *out, /* Size is in1_size + in2_size */
        const bn_digit *in1, size_t in1_size,
        const bn_digit *in2, size_t in2_size)
{
  size_t out_size = in1_size + in2_size;
  bn_digit *pprod;
  size_t pprod_size;
  size_t i;

  /* Zero fill the output so we can add into it */
  memset(out, 0, sizeof(out[0]) * out_size);

  /* Remove leading zeros */
  while (in1_size != 0U && in1[in1_size-1U] == 0U) {
    out[--out_size] = 0U;
  }
  while (in2_size != 0U && in2[in2_size-1U] == 0U) {
    out[--out_size] = 0U;
  }

  /* Allocate partial product */
  pprod_size = in2_size * 2;
  pprod = mrb_calloc(mrb, pprod_size, sizeof(pprod[0]));

  /* Main loop */
  for (i = 0; i < in1_size; i += in2_size) {
    size_t in1part_size = in1_size - i;
    size_t pprod_size2;
    if (in1part_size > in2_size) {
      in1part_size = in2_size;
    }
    bn_mul_recursive(mrb, pprod, in1+i, in1part_size, in2, in2_size);
    pprod_size2 = in1part_size + in2_size;
    bn_add_basic(out+i, out+i, pprod_size2, pprod, pprod_size2);
  }

  mrb_free(mrb, pprod);
}

/* Multiply:  Karatsuba algorithm */
static void
bn_mul_recursive(
        mrb_state *mrb,
        bn_digit *out, /* Size is in1_size + in2_size */
        const bn_digit *in1, size_t in1_size,
        const bn_digit *in2, size_t in2_size)
{
  size_t out_size = in1_size + in2_size;
  size_t split;
  bn_digit const *in1lo, *in1hi, *in2lo, *in2hi;
  size_t in1lo_size, in1hi_size, in2lo_size, in2hi_size;
  bn_digit *lprod, *uprod, *sum1, *sum2, *cprod;
  size_t lprod_size, uprod_size, sum1_size, sum2_size, cprod_size;

  /* Remove leading zeros */
  while (in1_size != 0U && in1[in1_size-1U] == 0U) {
    out[--out_size] = 0U;
    --in1_size;
  }
  while (in2_size != 0U && in2[in2_size-1U] == 0U) {
    out[--out_size] = 0U;
    --in2_size;
  }

  /* Let in1 be the longer input */
  if (in1_size < in2_size) {
    bn_digit const *sp;
    size_t sl;
    sp = in1;
    in1 = in2;
    in2 = sp;
    sl = in1_size;
    in1_size = in2_size;
    in2_size = sl;
  }

  /* Basis of recursion */
  if (in2_size < MRB_BIGNUM_MUL_RECURSION_CUTOFF) {
    bn_mul_basic(out, in1, in1_size, in2, in2_size);
    return;
  }

  /* Split the inputs */
  split = in1_size / 2;
  if (split >= in2_size) {
    /* Go to "lopsided" multiply if that can be done to advantage */
    bn_mul_lopsided(mrb, out, in1, in1_size, in2, in2_size);
    return;
  }
  in1lo = in1;
  in1lo_size = split;
  in1hi = in1 + split;
  in1hi_size = in1_size - split;
  in2lo = in2;
  in2lo_size = split;
  in2hi = in2 + split;
  in2hi_size = in2_size - split;

  /* Compute the lower and upper products */
  lprod = out;
  lprod_size = split * 2U;
  bn_mul_recursive(mrb, lprod, in1lo, in1lo_size, in2lo, in2lo_size);
  uprod = out + lprod_size;
  uprod_size = out_size - lprod_size;
  bn_mul_recursive(mrb, uprod, in1hi, in1hi_size, in2hi, in2hi_size);

  /* Compute the center product: */
  /* sum1 = in1hi + in1lo */
  sum1_size = (in1hi_size > in1lo_size ? in1hi_size : in1lo_size) + 1U;
  sum1 = mrb_calloc(mrb, sizeof(sum1[0]), sum1_size);
  sum1[sum1_size-1U] = bn_add_basic(sum1, in1hi, in1hi_size, in1lo, in1lo_size);
  /* sum2 = in2hi + in2lo */
  sum2_size = (in2hi_size > in2lo_size ? in2hi_size : in2lo_size) + 1U;
  sum2 = mrb_calloc(mrb, sizeof(sum2[0]), sum2_size);
  sum2[sum2_size-1U] = bn_add_basic(sum2, in2hi, in2hi_size, in2lo, in2lo_size);
  /* cprod = sum1 * sum2 */
  cprod_size = sum1_size + sum2_size;
  cprod = mrb_calloc(mrb, sizeof(cprod[0]), cprod_size);
  bn_mul_recursive(mrb, cprod, sum1, sum1_size, sum2, sum2_size);
  /* cprod = sum1 * sum2 - uprod - lprod */
  bn_sub_basic(cprod, cprod, cprod_size, uprod, uprod_size);
  bn_sub_basic(cprod, cprod, cprod_size, lprod, lprod_size);
  /* Add the center product to the final product */
  while (cprod_size != 0U && cprod[cprod_size-1U] == 0U) { --cprod_size; }
  bn_add_basic(out+split, out+split, out_size-split, cprod, cprod_size);

  mrb_free(mrb, sum1);
  mrb_free(mrb, sum2);
  mrb_free(mrb, cprod);
}
#endif /* MRB_BIGNUM_ENABLE_RECURSION */

/* Basic squaring */
static void
bn_sqr_basic(bn_digit *out, const bn_digit *in1, size_t in1_size)
{
  size_t out_size = in1_size * 2U;

  /* Remove leading zeros */
  while (in1_size != 0U && in1[in1_size-1U] == 0U) {
    --in1_size;
    out[--out_size] = 0U;
    out[--out_size] = 0U;
  }
  out_size = in1_size * 2U;

  /* Initialize the output */
  memset(out, 0, in1_size * sizeof(out[0]));

  /* Elements in1[i] and in1[j] where i != j */
  for (size_t i = 0U; i+1U < in1_size; ++i) {
    bn_digit carry = 0U;
    for (size_t j = i+1U; j < in1_size; ++j) {
      bn_dbl_digit prod = (bn_dbl_digit)in1[i] * in1[j] + out[i+j] + carry;
      out[i+j] = (bn_digit)prod;
      carry = (bn_digit)(prod >> MRB_BIGNUM_BIT);
    }
    out[i+in1_size] = carry;
  }
  /* Double these elements */
  bn_add_basic(out, out, out_size, out, out_size);

  /* Elements in1[i] and in1[j] where i == j */
  {
    unsigned carry = 0U;
    size_t j = 0U;
    for (size_t i = 0U; i < in1_size; ++i) {
      bn_dbl_digit prod = (bn_dbl_digit)in1[i] * in1[i];
      bn_digit sum;
      sum = out[j] + (bn_digit)prod + carry;
      if (sum < out[j]) { carry = 1U; }
      if (sum > out[j]) { carry = 0U; }
      out[j++] = sum;
      sum = out[j] + (bn_digit)(prod >> MRB_BIGNUM_BIT) + carry;
      if (sum < out[j]) { carry = 1U; }
      if (sum > out[j]) { carry = 0U; }
      out[j++] = sum;
    }
  }
}

#ifdef MRB_BIGNUM_ENABLE_RECURSION
/* Recursive squaring */
static void
bn_sqr_recursive(mrb_state *mrb, bn_digit *out,
        const bn_digit *in1, size_t in1_size)
{
  size_t out_size = 2U * in1_size;
  size_t split;
  bn_digit const *in1lo, *in1hi;
  size_t in1lo_size, in1hi_size;
  bn_digit *lprod, *uprod, *sum, *cprod;
  size_t lprod_size, uprod_size, sum_size, cprod_size;

  /* Remove leading zeros */
  while (in1_size != 0U && in1[in1_size-1U] == 0U) {
    --in1_size;
    out[--out_size] = 0U;
    out[--out_size] = 0U;
  }

  /* Basis of recursion */
  if (in1_size < MRB_BIGNUM_SQR_RECURSION_CUTOFF) {
    bn_sqr_basic(out, in1, in1_size);
    return;
  }

  /* Split the input */
  split = in1_size / 2U;
  in1lo = in1;
  in1lo_size = split;
  in1hi = in1 + split;
  in1hi_size = in1_size - split;

  /* Compute the lower product */
  lprod = out;
  lprod_size = in1lo_size * 2U;
  bn_sqr_recursive(mrb, lprod, in1lo, in1lo_size);

  /* Compute the upper product */
  uprod = out + lprod_size;
  uprod_size = out_size - lprod_size;
  bn_sqr_recursive(mrb, uprod, in1hi, in1hi_size);

  /* Add in1 and in2 */
  sum_size = (in1lo_size > in1hi_size ? in1lo_size : in1hi_size) + 1U;
  sum = mrb_calloc(mrb, sum_size, sizeof(sum[0]));
  sum[sum_size-1U] = bn_add_basic(sum, in1hi, in1hi_size, in1lo, in1lo_size);
  while (sum_size != 0U && sum[sum_size-1U] == 0U) { --sum_size; }

  /* Compute the center product */
  cprod_size = sum_size * 2U;
  cprod = mrb_calloc(mrb, cprod_size, sizeof(cprod[0]));
  bn_sqr_recursive(mrb, cprod, sum, sum_size);
  bn_sub_basic(cprod, cprod, cprod_size, lprod, lprod_size);
  bn_sub_basic(cprod, cprod, cprod_size, uprod, uprod_size);
  while (cprod_size != 0U && cprod[cprod_size-1U] == 0U) { --cprod_size; }

  /* Add the center product to the final product */
  bn_add_basic(out + split, out + split, out_size - split, cprod, cprod_size);

  mrb_free(mrb, sum);
  mrb_free(mrb, cprod);
}
#endif /* MRB_BIGNUM_ENABLE_RECURSION */

/* Multiply */
struct Bignum *
bn_mul(mrb_state *mrb, struct Bignum const *in1, struct Bignum const *in2)
{
  struct Bignum *out = bn_alloc(mrb, in1->len + in2->len);

#ifdef MRB_BIGNUM_ENABLE_RECURSION
  if (in1->digits == in2->digits && in1->len == in2->len) {
    bn_sqr_recursive(mrb, out->digits, in1->digits, in1->len);
  }
  else {
    bn_mul_recursive(mrb, out->digits, in1->digits, in1->len,
            in2->digits, in2->len);
  }
#else
  if (in1->digits == in2->digits && in1->len == in2->len) {
    bn_sqr_basic(out->digits, in1->digits, in1->len);
  }
  else {
    bn_mul_basic(out->digits, in1->digits, in1->len, in2->digits, in2->len);
  }
#endif

  out->negative = (in1->negative != 0) ^ (in2->negative != 0);
  return bn_normalize(out);
}

/* Divide in1 by a single digit, and return the remainder */
/* Used by bn_div_basic when the divisor is a single digit, and by
   bn_to_str_basic */
static bn_digit
bn_div_single(bn_digit *out, bn_digit const *in1, size_t in1_size, bn_digit in2)
{
  bn_digit rem;
  size_t i;

  rem = 0;
  for (i = in1_size; i-- != 0; ) {
    bn_dbl_digit tmp = ((bn_dbl_digit)rem << MRB_BIGNUM_BIT) | in1[i];
    if (out != NULL) {
        out[i] = (bn_digit)(tmp / in2);
    }
    rem = (bn_digit)(tmp % in2);
  }
  return rem;
}

/* Divide:  Basic algorithm */
static void
bn_div_basic(
        mrb_state *mrb,
        bn_digit *quo, /* Size is in1_size; may be NULL */
        bn_digit *rem, /* Size is in2_size; may be NULL */
        const bn_digit *in1, size_t in1_size,
        const bn_digit *in2, size_t in2_size)
{
  bn_digit *prem, *prod;
  size_t prem_size, prod_size;
  bn_digit trial_denom;
  size_t trial_denom_offset;
  unsigned trial_denom_shift;

  /* Zero fill the outputs */
  if (quo != NULL) {
    memset(quo, 0, sizeof(quo[0])*in1_size);
  }
  if (rem != NULL) {
    memset(rem, 0, sizeof(rem[0])*in2_size);
  }

  /* Remove leading zeros */
  while (in1_size != 0U && in1[in1_size-1U] == 0U) { --in1_size; }
  while (in2_size != 0U && in2[in2_size-1U] == 0U) { --in2_size; }

  /* Reject division by zero */
  if (in2_size == 0U) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  /* Quickly deal with this case, which would otherwise cause a segfault */
  if (in1_size < in2_size) {
    /* quo is already zero */
    if (rem != NULL) {
      memcpy(rem, in2, sizeof(rem[0])*in2_size);
    }
    return;
  }

  /* The main loop breaks if there's only one digit to divide by, because
     it needs trial_denom to have the top bit set */
  if (in2_size  == 1) {
    bn_digit r = bn_div_single(quo, in1, in1_size, in2[0]);
    if (rem != NULL) {
      rem[0] = r;
    }
    return;
  }

  /* Create a copy of in1; this will be the partial remainder */
  prem_size = in1_size;
  prem = mrb_calloc(mrb, prem_size, sizeof(prem[0]));
  memcpy(prem, in1, in1_size * sizeof(prem[0]));

  /* Allocate memory for the partial product */
  prod_size = in2_size + 2U;
  prod = mrb_calloc(mrb, prod_size, sizeof(prod[0]));

  /* The trial denominator is the top MRB_BIGNUM_BIT bits of in2, plus one,
     or in2 itself if in2 has only one digit. */
  trial_denom = in2[in2_size-1U];   /* top MRB_BIGNUM_BIT bits */
  trial_denom_offset = in2_size-1U; /* index of in2 where trial_denom bit 0 lies */
  trial_denom_shift = 0U;           /* number of bits to the right of trial_denom */
  /* Shift trial_denom so the top bit is 1 */
  while ((trial_denom & ((bn_digit)1 << (MRB_BIGNUM_BIT-1))) == 0U) {
    ++trial_denom_shift;
    trial_denom <<= 1;
  }
  /* Add bits from the second most significant digit */
  if (trial_denom_shift != 0) {
    trial_denom_shift = MRB_BIGNUM_BIT - trial_denom_shift;
    trial_denom |= in2[in2_size-2U] >> trial_denom_shift;
    --trial_denom_offset;
  }
  /* Overstate the trial denominator so arithmetic does not overflow */
  ++trial_denom;
  /* The above increment may overflow.  If that happens, trial_denom is
     equal to 0.  That case is handled specially in the main loop. */

  /* Invariant for the main loop:  quo * in2 + prem = in1 */
  /* When prem < in2, quo is the final quotient and prem is the final
     remainder */
  while (bn_cmp_basic(prem, prem_size, in2, in2_size) >= 0) {
    /* The trial numerator is the top MRB_BIGNUM_BIT*2 bits of prem. */
    bn_digit trial_num[2];    /* top MRB_BIGNUM_BIT*2 bits */
    size_t trial_num_offset;  /* index of in2 where trial_num[0] bit 0 lies */
    unsigned trial_num_shift; /* number of bits to the right of trial_num[0] */
    bn_digit trial_quo[2];    /* trial quotient */
    size_t trial_quo_offset;  /* index for shifting the product */
    unsigned trial_quo_shift; /* bits to shift the product */
    if (prem_size == 1U) {
      trial_num[0] = prem[0];
      trial_num[1] = 0U;
      trial_num_offset = 0U;
      trial_num_shift = 0U;
    }
    else {
      trial_num[0] = prem[prem_size-2U];
      trial_num[1] = prem[prem_size-1U];
      trial_num_offset = prem_size-2U;
      trial_num_shift = 0U;
      if (prem_size > 2U) {
        /* Shift trial_num[1] so the top bit is 1 */
        while ((trial_num[1] & ((bn_digit)1 << (MRB_BIGNUM_BIT-1))) == 0U) {
          ++trial_num_shift;
          trial_num[1] <<= 1;
        }
        if (trial_num_shift != 0U) {
          /* Shift trial_num[0] to match */
          trial_num[1] |= (trial_num[0] >> (MRB_BIGNUM_BIT - trial_num_shift));
          trial_num[0] <<= trial_num_shift;
          trial_num_shift = MRB_BIGNUM_BIT - trial_num_shift;
          trial_num[0] |= prem[prem_size-3U] >> trial_num_shift;
          --trial_num_offset;
        }
      }
    }

    /* The offset and shift of the trial numerator must never be less than
       that of the trial denominator */
    if (trial_num_offset < trial_denom_offset
    ||  (trial_num_offset == trial_denom_offset && trial_num_shift < trial_denom_shift)) {
      unsigned shift = (trial_denom_offset - trial_num_offset)*MRB_BIGNUM_BIT
                     +  trial_denom_shift - trial_num_shift;
      if (shift >= MRB_BIGNUM_BIT) {
        trial_num[0] = trial_num[1];
        trial_num[1] = 0U;
        shift -= MRB_BIGNUM_BIT;
      }
      if (shift != 0U) {
        trial_num[0] = (trial_num[0] >> shift)
                     | (trial_num[1] << (MRB_BIGNUM_BIT - shift));
        trial_num[1] >>= shift;
      }
      trial_num_offset = trial_denom_offset;
      trial_num_shift = trial_denom_shift;
    }

    /* Do trial division */
    if (trial_denom == 0U) {
      /* Overstating the trial denominator caused an overflow;
         the actual value is 1 << MRB_BIGNUM_BIT */
      trial_quo[0] = trial_num[1];
    }
    else {
      /* If division would overflow, knock a bit off the trial numerator */
      if (trial_num[1] >= trial_denom) {
        trial_num[0] = (trial_num[0] >> 1) | (trial_num[1] << (MRB_BIGNUM_BIT -1));
        trial_num[1] >>= 1;
        ++trial_num_shift;
        if (trial_num_shift >= MRB_BIGNUM_BIT) {
          trial_num_shift = 0U;
          ++trial_num_offset;
        }
      }
      trial_quo[0] = (((bn_dbl_digit)trial_num[1] << MRB_BIGNUM_BIT)
                      + trial_num[0]) / trial_denom;
    }
    if (trial_quo[0] == 0U) {
      /* Because prem >= in2, the trial quotient can always be at
         least 1; and it must, to avoid an infinite loop */
      trial_quo[0] = 1U;
    }
    trial_quo_offset = trial_num_offset - trial_denom_offset;
    trial_quo_shift = trial_num_shift - trial_denom_shift;
    if (trial_num_shift < trial_denom_shift) {
      trial_quo_shift += MRB_BIGNUM_BIT;
      --trial_quo_offset;
    }

    /* Add the trial quotient to the final quotient */
    if (trial_quo_shift == 0U) {
      trial_quo[1] = 0U;
    }
    else {
      trial_quo[1] = trial_quo[0] >> (MRB_BIGNUM_BIT - trial_quo_shift);
      trial_quo[0] <<= trial_quo_shift;
    }
    if (quo != NULL) {
      bn_add_basic(
              quo + trial_quo_offset,
              quo + trial_quo_offset, in1_size - trial_quo_offset,
              trial_quo, trial_quo[1] == 0U ? 1U : 2U);
    }

    /* Multiply to form the partial product */
    bn_mul_basic(prod, in2, in2_size, trial_quo, 2U);
    /* Subtract from the partial remainder */
    bn_sub_basic(
            prem + trial_quo_offset,
            prem + trial_quo_offset, prem_size - trial_quo_offset,
            prod, prod_size);
    /* Shrink the partial remainder as it decreases */
    while (prem_size != 0U && prem[prem_size-1U] == 0U) { --prem_size; }
  }

  /* Fill the final remainder */
  if (rem != NULL) {
    memcpy(rem, prem, sizeof(rem[0])*in2_size);
  }

  mrb_free(mrb, prem);
  mrb_free(mrb, prod);
}

#ifdef MRB_BIGNUM_ENABLE_RECURSION
/* Divide:  Recursive algorithm */
static void
bn_div_recursive(
        mrb_state *mrb,
        bn_digit *quo, /* Size is in1_size; may be NULL */
        bn_digit *rem, /* Size is in2_size; may be NULL */
        const bn_digit *in1, size_t in1_size,
        const bn_digit *in2, size_t in2_size)
{
  static const bn_digit one = 1U;
  size_t split;
  bn_digit *prem, *prod, *trial_quo, *trial_denom;
  size_t prem_size, prod_size, trial_quo_size, trial_denom_size;
  size_t trial_denom_offset;

  /* Zero fill the outputs */
  if (quo != NULL) {
    memset(quo, 0, sizeof(quo[0])*in1_size);
  }
  if (rem != NULL) {
    memset(rem, 0, sizeof(rem[0])*in2_size);
  }

  /* Remove leading zeros */
  while (in1_size != 0U && in1[in1_size-1U] == 0U) { --in1_size; }
  while (in2_size != 0U && in2[in2_size-1U] == 0U) { --in2_size; }

  /* Reject division by zero */
  if (in2_size == 0U) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  /* Basis of recursion */
  if (in2_size < MRB_BIGNUM_DIV_RECURSION_CUTOFF
  ||  in2_size + MRB_BIGNUM_DIV_RECURSION_CUTOFF >= in1_size) {
    bn_div_basic(mrb, quo, rem, in1, in1_size, in2, in2_size);
    return;
  }

  /* Determine split size */
  split = in1_size - in2_size;
  if (split > in2_size) {
    split = in2_size;
  }
  split /= 2U;

  /* Create a copy of in1; this will be the partial remainder */
  prem_size = in1_size;
  prem = mrb_calloc(mrb, prem_size, sizeof(prem[0]));
  memcpy(prem, in1, in1_size * sizeof(prem[0]));

  /* Allocate memory for the partial product */
  prod_size = in2_size + prem_size;
  prod = mrb_calloc(mrb, prod_size, sizeof(prod[0]));

  /* Allocate memory for the trial quotient */
  trial_quo_size = prem_size;
  trial_quo = mrb_calloc(mrb, trial_quo_size, sizeof(trial_quo[0]));

  /* Determine the trial denominator */
  trial_denom_size = split + 1U;
  trial_denom = mrb_calloc(mrb, trial_denom_size, sizeof(trial_denom[0]));
  trial_denom_offset = in2_size - split;
  memcpy(trial_denom, in2 + trial_denom_offset, split*sizeof(trial_denom[0]));
  bn_add_basic(trial_denom, trial_denom, trial_denom_size, &one, 1U);
  while (trial_denom_size != 0U && trial_denom[trial_denom_size-1U] == 0U) {
    --trial_denom_size;
  }

  /* Invariant for the main loop:  quo * in2 + prem = in1 */
  /* When prem < in2, quo is the final quotient and prem is the final
     remainder */
  while (bn_cmp_basic(prem, prem_size, in2, in2_size) >= 0) {
    bn_digit const *trial_num;
    size_t trial_num_size, trial_num_offset, trial_quo_size2, trial_quo_offset;
    size_t prod_size2;

    /* The trial numerator is the top split*2 digits (at most) of prem. */
    trial_num_size = split * 2U;

    /* Limit the trial numerator size to the partial remainder size */
    if (prem_size < trial_num_size) {
      trial_num_offset = 0U;
    }
    else {
      trial_num_offset = prem_size - trial_num_size;
    }
    /* trial_num_offset must not be less than trial_denom_offset, else
       trial_quo_offset would be negative */
    if (trial_num_offset < trial_denom_offset) {
      trial_num_offset = trial_denom_offset;
    }
    trial_num_size = prem_size - trial_num_offset;
    trial_num = prem + trial_num_offset;

    /* Compute the trial quotient */
    bn_div_recursive(
            mrb,
            trial_quo, NULL,
            trial_num, trial_num_size,
            trial_denom, trial_denom_size);
    trial_quo_size2 = trial_num_size;
    while (trial_quo_size2 != 0U && trial_quo[trial_quo_size2-1U] == 0U) {
      --trial_quo_size2;
    }
    if (trial_quo_size2 == 0U) {
      trial_quo_size2 = 1U;
      trial_quo[0U] = 1U;
    }
    trial_quo_offset = trial_num_offset - trial_denom_offset;

    /* Add the trial quotient to the final quotient */
    if (quo != NULL) {
      bn_add_basic(
              quo + trial_quo_offset,
              quo + trial_quo_offset, in1_size - trial_quo_offset,
              trial_quo, trial_quo_size2);
    }

    /* Multiply the trial quotient by in2 */
    bn_mul_recursive(mrb, prod, trial_quo, trial_quo_size2, in2, in2_size);
    prod_size2 = trial_quo_size2 + in2_size;
    while (prod_size2 != 0U && prod[prod_size2-1U] == 0U) { --prod_size2; }

    /* Subtract the product from prem */
    bn_sub_basic(
            prem + trial_quo_offset,
            prem + trial_quo_offset, prem_size - trial_quo_offset,
            prod, prod_size2);
    while (prem_size != 0U && prem[prem_size-1U] == 0U) { --prem_size; }
  }

  /* Copy prem to rem */
  if (rem) {
    memcpy(rem, prem, in2_size*sizeof(rem[0]));
  }

  mrb_free(mrb, trial_denom);
  mrb_free(mrb, prem);
  mrb_free(mrb, prod);
  mrb_free(mrb, trial_quo);
}
#endif /* MRB_BIGNUM_ENABLE_RECURSION */

/* Quotient and remainder, disregarding signs */
static void
bn_divmod_unsigned(
        mrb_state *mrb,
        struct Bignum **quo, struct Bignum **rem,
        struct Bignum const *in1, struct Bignum const *in2)
{
  struct Bignum *q = bn_alloc(mrb, in1->len);
  struct Bignum *r = bn_alloc(mrb, in2->len);

#ifdef MRB_BIGNUM_ENABLE_RECURSION
  bn_div_recursive(mrb, q->digits, r->digits,
          in1->digits, in1->len, in2->digits, in2->len);
#else
  bn_div_basic(mrb, q->digits, r->digits,
          in1->digits, in1->len, in2->digits, in2->len);
#endif

  *quo = bn_normalize(q);
  *rem = bn_normalize(r);
}

/* Quotient and remainder */
static void
bn_divmod(mrb_state *mrb,
      struct Bignum **quo, struct Bignum **rem,
      struct Bignum const *in1, struct Bignum const *in2)
{
  struct Bignum *q, *r;
  bn_divmod_unsigned(mrb, &q, &r, in1, in2);
  q->negative = (in1->negative != 0) != (in2->negative != 0);
  r->negative = in1->negative;

  /* Division rounds down */
  bn_normalize(q);
  bn_normalize(r);
  if (q->negative && r->len != 0) {
    static const bn_digit one = 1;
    /* Don't bother fixing outputs that aren't going to be used */
    if (quo) {
      /* q += 1; do in place unless it carries */
      if (bn_add_basic(q->digits, q->digits, q->len, &one, 1)) {
        struct Bignum *q2 = bn_alloc(mrb, q->len + 1);
        q2->digits[q->len] = 1;
        bn_free(mrb, q);
        q = q2;
      }
    }
    if (rem) {
      struct Bignum *r2 = bn_add(mrb, r, in2, FALSE);
      bn_free(mrb, r);
      r = r2;
    }
  }

  if (quo) {
    *quo = q;
  }
  else {
    bn_free(mrb, q);
  }
  if (rem) {
    *rem = r;
  }
  else {
    bn_free(mrb, r);
  }
}

/* Divide */
static struct Bignum *
bn_div(mrb_state *mrb, struct Bignum const *in1, struct Bignum const *in2)
{
  struct Bignum *out;
  bn_divmod(mrb, &out, NULL, in1, in2);
  return out;
}

/* Modulo */
static struct Bignum *
bn_mod(mrb_state *mrb, struct Bignum const *in1, struct Bignum const *in2)
{
  struct Bignum *out;
  bn_divmod(mrb, NULL, &out, in1, in2);
  return out;
}

/* Common code for bitwise AND, OR and XOR operators */
static struct Bignum *
bn_bitwise(mrb_state *mrb, struct Bignum const *in1, struct Bignum const *in2,
        bn_digit (*op)(bn_digit in1, bn_digit in2))
{
  size_t i;
  bn_digit dig1, dig2;
  struct Bignum *out;
  mrb_bool not1, not2;

  /* Let in1 be the longer input */
  if (in1->len < in2->len) {
    struct Bignum const *swp;
    swp = in1;
    in1 = in2;
    in2 = swp;
  }

  out = bn_alloc(mrb, in1->len);

  not1 = FALSE;
  not2 = FALSE;

  /* To the shorter input */
  for (i = 0; i < in2->len; ++i) {
    dig1 = in1->digits[i];
    if (in1->negative) {
      dig1 = ~dig1;
      if (!not1) {
        ++dig1;
        not1 = dig1 != 0;
      }
    }
    dig2 = in2->digits[i];
    if (in2->negative) {
      dig2 = ~dig2;
      if (!not2) {
        ++dig2;
        not2 = dig2 != 0;
      }
    }

    out->digits[i] = (*op)(dig1, dig2);
  }

  /* To the longer input */
  dig2 = in2->negative ? (bn_digit)-1 : 0;
  for (; i < in1->len; ++i) {
    dig1 = in1->digits[i];
    if (in1->negative) {
      dig1 = ~dig1;
      if (!not1) {
        ++dig1;
        not1 = dig1 != 0;
      }
    }

    out->digits[i] = (*op)(dig1, dig2);
  }

  /* Sign bits */
  out->negative = (*op)(in1->negative, in2->negative);
  if (out->negative) {
    for (i = 0; i < out->len && out->digits[i] == 0; ++i) {}
    if (i < out->len) {
      out->digits[i] = -out->digits[i];
      ++i;
    }
    for (; i < out->len; ++i) {
      out->digits[i] = ~out->digits[i];
    }
  }

  return bn_normalize(out);
}

/* Bitwise AND */
static bn_digit
bn_and_op(bn_digit in1, bn_digit in2)
{
  return in1 & in2;
}

static struct Bignum *
bn_and(mrb_state *mrb, struct Bignum const *in1, struct Bignum const *in2)
{
  return bn_bitwise(mrb, in1, in2, bn_and_op);
}

/* Bitwise OR */
static bn_digit
bn_or_op(bn_digit in1, bn_digit in2)
{
  return in1 | in2;
}

static struct Bignum *
bn_or(mrb_state *mrb, struct Bignum const *in1, struct Bignum const *in2)
{
  return bn_bitwise(mrb, in1, in2, bn_or_op);
}

/* Bitwise XOR */
static bn_digit
bn_xor_op(bn_digit in1, bn_digit in2)
{
  return in1 ^ in2;
}

static struct Bignum *
bn_xor(mrb_state *mrb, struct Bignum const *in1, struct Bignum const *in2)
{
  return bn_bitwise(mrb, in1, in2, bn_xor_op);
}

/* Left shift a Bignum by an unsigned shift distance */
static struct Bignum *
bn_lshift_unsigned(mrb_state *mrb, struct Bignum const *in1, uint64_t in2)
{
  uint64_t digit_shift = in2 / MRB_BIGNUM_BIT;
  unsigned bit_shift   = in2 % MRB_BIGNUM_BIT;
  struct Bignum *out;
  size_t out_size;

  /* Compute the size of the output and detect overflow */
  if (digit_shift > SIZE_MAX) {
    goto overflow;
  }
  out_size = in1->len + digit_shift;
  if (out_size < digit_shift) {
    goto overflow;
  }
  if (bit_shift != 0) {
    ++out_size;
    if (out_size == 0) {
      goto overflow;
    }
  }

  out = bn_alloc(mrb, out_size);

  if (bit_shift == 0) {
    /* Avoid undefined behavior in the shift */
    memcpy(out->digits + digit_shift, in1->digits,
            in1->len * sizeof(out->digits[0]));
  }
  else {
    bn_digit carry = 0;
    size_t i;
    for (i = 0; i < in1->len; ++i) {
      out->digits[i+digit_shift] = (in1->digits[i] << bit_shift) | carry;
      carry = in1->digits[i] >> (MRB_BIGNUM_BIT - bit_shift);
    }
    out->digits[i+digit_shift] = carry;
  }

  out->negative = in1->negative;
  return bn_normalize(out);

overflow:
  mrb_raise(mrb, E_RUNTIME_ERROR, "Left shift too large");
  return NULL;
}

/* Right shift a Bignum by an unsigned shift distance */
static struct Bignum *
bn_rshift_unsigned(mrb_state *mrb, struct Bignum const *in1, uint64_t in2)
{
  uint64_t digit_shift = in2 / MRB_BIGNUM_BIT;
  unsigned bit_shift   = in2 % MRB_BIGNUM_BIT;
  struct Bignum *out;
  mrb_bool round;
  size_t i;

  if (digit_shift >= in1->len) {
    return fixnum_to_bignum(mrb, in1->negative ? -1 : 0);
  }

  out = bn_alloc(mrb, in1->len - digit_shift);

  /* Division rounds down */
  round = FALSE;
  if (in1->negative) {
    for (i = 0; i < digit_shift && !round; ++i) {
      round = in1->digits[i] != 0;
    }
  }

  if (bit_shift == 0) {
    /* Avoid undefined behavior in the shift */
    memcpy(out->digits, in1->digits + digit_shift,
            out->len * sizeof(out->digits[0]));
  }
  else {
    bn_digit carry = 0;
    for (i = out->len; i-- != 0; ) {
      out->digits[i] = carry | (in1->digits[i+digit_shift] >> bit_shift);
      carry = in1->digits[i+digit_shift] << (MRB_BIGNUM_BIT - bit_shift);
    }
    if (in1->negative) {
      round |= carry != 0;
    }
  }

  if (round) {
    /* Increment in place unless that carries */
    static const bn_digit one = 1;
    if (bn_add_basic(out->digits, out->digits, out->len, &one, 1) != 0) {
      struct Bignum *out2 = bn_alloc(mrb,  out->len + 1);
      out2->digits[out->len] = 1;
      bn_free(mrb, out);
      out = out2;
    }
  }

  out->negative = in1->negative;
  return bn_normalize(out);
}

/* Left shift a Bignum by a signed shift distance */
static struct Bignum *
bn_lshift(mrb_state *mrb, struct Bignum const *in1, int64_t in2)
{
  if (in2 < 0) {
    return bn_rshift_unsigned(mrb, in1, -(uint64_t)in2);
  }
  else {
    return bn_lshift_unsigned(mrb, in1, +(uint64_t)in2);
  }
}

/* Right shift a Bignum by a signed shift distance */
static struct Bignum *
bn_rshift(mrb_state *mrb, struct Bignum const *in1, int64_t in2)
{
  if (in2 < 0) {
    return bn_lshift_unsigned(mrb, in1, -(uint64_t)in2);
  }
  else {
    return bn_rshift_unsigned(mrb, in1, +(uint64_t)in2);
  }
}

/* Raise a Bignum to a non-negative power */
static struct Bignum *
bn_pow(mrb_state *mrb, struct Bignum const *x, uint64_t y)
{
  struct Bignum *z1, *z2;
  struct Bignum *p1, *p2;

  /* z1 <- 1 */
  z1 = fixnum_to_bignum(mrb, 1);

  /* p1 <- x */
  p1 = bn_alloc(mrb, x->len);
  p1->negative = x->negative;
  memcpy(p1->digits, x->digits, p1->len * sizeof(p1->digits[0]));

  while (y != 0) {
    if ((y & 1) != 0) {
      z2 = bn_mul(mrb, z1, p1);
      bn_free(mrb, z1);
      z1 = z2;
    }
    y >>= 1;
    if (y != 0) {
      p2 = bn_mul(mrb, p1, p1);
      bn_free(mrb, p1);
      p1 = p2;
    }
  }

  return z1;
}

#ifdef MRB_BIGNUM_ENABLE_RECURSION
struct BignumDivisor
{
  size_t power;
  struct Bignum *divisor;
};

/* Precompute divisors for conversion to and from string */
static struct BignumDivisor *
bn_compute_divisors(mrb_state *mrb, size_t size, unsigned base)
{
  bn_digit bigbase, power;
  unsigned bigdigits;
  unsigned count, i;
  struct BignumDivisor *divisors;

  /* Power of base that will fit in a bn_digit */
  bigbase = base;
  bigdigits = 1;
  while (TRUE) {
    bn_digit bigbase2 = bigbase * base;
    if (bigbase2/base != bigbase) {
      break;
    }
    bigbase = bigbase2;
    ++bigdigits;
  }

  /* Count the divisors to be generated */
  power = bigdigits;
  count = 1;
  while (TRUE) {
    bn_digit power2 = power << 1;
    if ((power2 >> 1) != power || power >= size) {
      break;
    }
    power = power2;
    ++count;
  }

  /* Allocate memory for the array */
  divisors = mrb_calloc(mrb, count + 1, sizeof(divisors[0]));

  /* Compute the divisors */
  divisors[0].power = bigdigits;
  divisors[0].divisor = bn_alloc(mrb, 1);
  divisors[0].divisor->digits[0] = bigbase;
  for (i = 1; i < count; ++i) {
    divisors[i].power = divisors[i-1].power << 1;
    divisors[i].divisor = bn_mul(mrb, divisors[i-1].divisor, divisors[i-1].divisor);
  }
  divisors[i].divisor = NULL;

  return divisors;
}

/* Find the best divisor for the given size */
static struct BignumDivisor const *
bn_find_divisor(struct BignumDivisor const *divisors, size_t size)
{
  unsigned i;

  for (i = 1; divisors[i].divisor != NULL && divisors[i].power < size; ++i) {}
  --i;
  return &divisors[i];
}

/* Free the divisors array */
static void
bn_free_divisors(mrb_state *mrb, struct BignumDivisor *divisors)
{
  unsigned i;

  for (i = 0; divisors[i].divisor != NULL; ++i) {
    bn_free(mrb, divisors[i].divisor);
  }
  bn_free(mrb, divisors);
}
#endif /* MRB_BIGNUM_ENABLE_RECURSION */

/* Convert Bignum to string, where the base is a power of two */
/* Sign is included */
static char *
bn_to_str_pow2(mrb_state *mrb, struct Bignum const *in1, unsigned logbase)
{
  size_t i, j;
  uint64_t bits;
  unsigned shift;
  char *str;
  size_t str_len;
  mrb_bool zero;

  /* Allocate string, with space for sign and terminating null */
  bits = (uint64_t)in1->len * MRB_BIGNUM_BIT;
  str_len = (bits + logbase - 1) / logbase;
  str = mrb_malloc(mrb, str_len + 2);

  /* Set indexes for the loop */
  bits = (uint64_t)str_len * logbase;
  i = 0;
  j     = bits / MRB_BIGNUM_BIT;
  shift = bits % MRB_BIGNUM_BIT;
  if (in1->negative) {
    str[i++] = '-';
  }

  /* This suppresses leading zeros */
  zero = TRUE;

  /* Convert */
  while (j != 0 || shift != 0) {
    unsigned digit;

    /* Decrement the index into the Bignum */
    if (shift < logbase) {
      --j;
      shift += MRB_BIGNUM_BIT;
    }
    shift -= logbase;

    /* Extract a digit */
    digit = in1->digits[j] >> shift;
    if (shift+logbase > MRB_BIGNUM_BIT && j+1 < in1->len) {
      /* Digit crosses a Bignum digit boundary */
      /* Can only happen if base == 8 or 32 (logbase == 3 or 5) */
      unsigned rbits = MRB_BIGNUM_BIT - shift; /* how many bits we have */
      digit |= in1->digits[j+1] << rbits;
    }
    digit &= (1 << logbase) - 1;

    /* Convert to character, suppressing leading zeros */
    if (digit != 0) {
      zero = FALSE;
    }
    if (!zero) {
      mrb_assert(i+1 < str_len + 2);
      str[i++] = mrb_digitmap[digit];
    }
  }

  /* Return the converted string */
  str[i] = 0;
  return str;
}

/* Basic, nonrecursive Bignum to string algorithm */
/* Used only for bases that are not powers of two */
/* Sign is not included; leading zeros are */
static void
bn_to_str_basic(
        mrb_state *mrb,
        char *str, size_t str_len,
        struct Bignum const *in1,
        unsigned base)
{
  struct Bignum *num;
  bn_digit bigbase;
  unsigned bigdigits;
  size_t i;

  /* Create a working copy of the input */
  num = bn_alloc(mrb, in1->len);
  memcpy(num->digits, in1->digits, in1->len * sizeof(num->digits[0]));

  /* Set bigbase to the largest power of base that fits in a bn_digit, and
     bigdigits such that base ** bigdigits = bigbase */
  bigbase = base;
  bigdigits = 1;
  while (1) {
    bn_digit bigbase2 = bigbase * base;
    if (bigbase2 / base != bigbase) {
      break; /* Overflow */
    }
    bigbase = bigbase2;
    ++bigdigits;
  }

  /* Convert */
  i = str_len;
  while (i != 0 && num->len != 0) {
    /* Extract bigdigits digits */
    unsigned j;
    bn_digit rem = bn_div_single(num->digits, num->digits, num->len, bigbase);
    while (num->len != 0 && num->digits[num->len-1] == 0) {
      --num->len;
    }
    for (j = 0; j < bigdigits && i != 0; ++j) {
      unsigned digit = rem % base;
      rem /= base;
      str[--i] = mrb_digitmap[digit];
    }
  }
  mrb_assert(num->len == 0);
  memset(str, '0', i);

  bn_free(mrb, num);
}

#ifdef MRB_BIGNUM_ENABLE_RECURSION
/* Recursive Bignum to string algorithm */
/* Used only for bases that are not powers of two */
/* Sign is not included; leading zeros are */
static void
bn_to_str_recursive(
        mrb_state *mrb,
        char *str, size_t str_len,
        struct Bignum const *in1,
        unsigned base,
        struct BignumDivisor const *divisors)
{
  size_t split;
  struct BignumDivisor const *divisor;
  struct Bignum *div, *quo, *rem;

  if (in1->len < MRB_BIGNUM_DIV_RECURSION_CUTOFF) {
    /* Basis of recursion */
    bn_to_str_basic(mrb, str, str_len, in1, base);
    return;
  }

  /* Split the input */
  divisor = bn_find_divisor(divisors, str_len);
  split = divisor->power;
  div = divisor->divisor;
  bn_divmod_unsigned(mrb, &quo, &rem, in1, div);
  mrb_assert(split < str_len);

  /* Convert the upper and lower halves */
  bn_to_str_recursive(mrb, str, str_len - split, quo, base, divisors);
  bn_free(mrb, quo);
  bn_to_str_recursive(mrb, str + str_len - split, split, rem, base, divisors);
  bn_free(mrb, rem);
}
#endif

/* Convert a Bignum to a string, using the given base */
/* The caller must ensure that the base is valid (0 or 2..36) */
static char *
bn_to_str(mrb_state *mrb, struct Bignum const *in1, unsigned base)
{
  unsigned bits;
  char *str;

  /* It's simpler to remove leading zeros if in1 != 0 */
  if (in1->len == 0) {
    str = mrb_malloc(mrb, 2);
    strcpy(str, "0");
    return str;
  }

  /* Build the string in reverse order */
  /* The allocation has one extra byte for the sign */
  for (bits = 1; (1 << bits) < base; ++bits) {}
  if ((1 << bits) == base) {
    /* Fast algorithm for base that is a power of two */
    str = bn_to_str_pow2(mrb, in1, bits);
  }
  else {
    size_t str_len;
    char *p, *q;

    /* Allocate memory for the string, allowing 1 byte for the sign and a bit
       of slop in case of roundoff error */
    str_len = F(ceil)((in1->len*MRB_BIGNUM_BIT)
            / (F(log)(base)/(mrb_float)0.69314718055994530942) + 1);
    str = mrb_malloc(mrb, str_len + 2);

    /* Set the sign */
    p = str;
    if (in1->negative) {
      *(p++) = '-';
    }
#ifdef MRB_BIGNUM_ENABLE_RECURSION
    {
      struct BignumDivisor *divisors;
      divisors = bn_compute_divisors(mrb, str_len, base);
      bn_to_str_recursive(mrb, p, str_len, in1, base, divisors);
      bn_free_divisors(mrb, divisors);
    }
#else
    bn_to_str_basic(mrb, p, str_len, in1, base);
#endif
    p[str_len] = 0;

    /* Remove leading zeros */
    q = p;
    while (*q == '0') {
      ++q;
    }
    if (q != p) {
      memmove(p, q, strlen(q) + 1);
    }
  }

  return str;
}

/* Multiply in1 in place by in2 and add in3 (as unsigned values) */
static bn_digit
bn_mul_single(struct Bignum *in1, bn_digit in2, bn_digit in3)
{
  bn_digit carry;
  bn_dbl_digit prod;
  size_t i;

  carry = in3;
  for (i = 0; i < in1->len; ++i) {
    prod = (bn_dbl_digit)in1->digits[i] * in2 + carry;
    in1->digits[i] = (bn_digit)prod;
    carry = (bn_digit)(prod >> MRB_BIGNUM_BIT);
  }

  return carry;
}

/* Convert a string to a Bignum using the given base */
/* The base is a power of two, equal to 1 << logbase */
/* Signs, prefixes and underscores are not processed here */
static struct Bignum *
bn_from_str_pow2(
        mrb_state *mrb,
        char const *str, size_t str_len,
        unsigned logbase)
{
  uint64_t bits;
  size_t digits;
  struct Bignum *num;
  size_t i, j;
  unsigned shift;

  /* Remove leading zeros */
  while (*str == '0' && str_len != 0) {
    ++str;
    --str_len;
  }

  /* Allocate the Bignum */
  bits = str_len * logbase;
  digits = (bits + MRB_BIGNUM_BIT - 1) / MRB_BIGNUM_BIT;
  num = bn_alloc(mrb, digits);

  /* Set indexes for the loop */
  j     = 0;
  shift = 0;

  /* Convert */
  for (i = str_len; i-- != 0; ) {
    char const *p;
    unsigned digit;

    p = strchr(mrb_digitmap, tolower(str[i]));
    mrb_assert(p != NULL);
    digit = (unsigned)(p - mrb_digitmap);
    mrb_assert(digit < (1 << logbase));
    num->digits[j] |= (bn_digit)digit << shift;
    if (shift + logbase > MRB_BIGNUM_BIT && j+1 < num->len) {
      /* String digit crosses a Bignum digit boundary */
      /* This is only possible if base == 8 or 32 */
      unsigned rbits = MRB_BIGNUM_BIT - shift; /* how many bits we have */
      num->digits[j+1] = digit >> rbits;
    }

    /* Advance the index for the Bignum */
    shift += logbase;
    if (shift >= MRB_BIGNUM_BIT) {
      shift -= MRB_BIGNUM_BIT;
      ++j;
    }
  }

  return num;
}

/* Convert a string to a Bignum using the given base */
/* The base is not a power of two */
/* Basic algorithm, without recursion */
/* Signs, prefixes and underscores are not processed here */
static struct Bignum *
bn_from_str_basic(
        mrb_state *mrb,
        char const *str, size_t str_len,
        unsigned base)
{
  size_t num_digits;
  uint64_t bits;
  struct Bignum *num;
  bn_digit bigbase, bdig, carry;
  unsigned bigdigits, passdigits;
  size_t i;

  /* Remove leading zeros */
  while ((*str == '0' || *str == '_') && str_len != 0) {
    ++str;
    --str_len;
  }

  /* Allocate the Bignum */
  bits = (uint64_t)F(ceil)(str_len * (F(log)(base)/(mrb_float)0.69314718055994530942) + 1);
  num_digits = (size_t)((bits + MRB_BIGNUM_BIT - 1)/MRB_BIGNUM_BIT);
  num = bn_alloc(mrb, num_digits);
  num->len = 0; /* for bn_mul_single */

  /* Set bigbase to the largest power of base that fits in a bn_digit, and
     bigdigits such that base ** bigdigits = bigbase */
  bigbase = base;
  bigdigits = 1;
  while (1) {
    bn_digit bigbase2 = bigbase * base;
    if (bigbase2 / base != bigbase) {
      break; /* Overflow */
    }
    bigbase = bigbase2;
    ++bigdigits;
  }

  /* Convert */
  passdigits = 0;
  bdig = 0;
  for (i = 0; i < str_len; ++i) {
    char const *p;
    unsigned digit;

    if (str[i] == '_') {
      continue;
    }
    p = strchr(mrb_digitmap, tolower(str[i]));
    mrb_assert(p != NULL);
    digit = (unsigned)(p - mrb_digitmap);
    mrb_assert(digit < base);
    bdig = bdig * base + digit;
    ++passdigits;
    if (passdigits >= bigdigits) {
      carry = bn_mul_single(num, bigbase, bdig);
      if (carry != 0) {
        mrb_assert(num->len < num_digits);
        num->digits[num->len++] = carry;
      }
      passdigits = 0;
      bdig = 0;
    }
  }

  if (passdigits != 0) {
    unsigned k;
    bigbase = base;
    for (k = 1; k < passdigits; ++k) {
      bigbase *= base;
    }
    carry = bn_mul_single(num, bigbase, bdig);
    if (carry != 0) {
      mrb_assert(num->len < num_digits);
      num->digits[num->len++] = carry;
    }
  }

  return num;
}

/* Convert a string to a Bignum using the given base */
/* The base is not a power of two */
/* Recursive algorithm */
/* Signs, prefixes and underscores are not processed here */
#ifdef MRB_BIGNUM_ENABLE_RECURSION
static struct Bignum *
bn_from_str_recursive(
        mrb_state *mrb,
        char const *str, size_t str_len,
        unsigned base,
        struct BignumDivisor const *divisors)
{
  size_t split;
  struct BignumDivisor const *divisor;
  struct Bignum *lnum, *rnum, *mul, *prod, *num;

  /* Remove leading zeros */
  while ((*str == '0' || *str == '_') && str_len != 0) {
    ++str;
    --str_len;
  }

  /* Basis of recursion */
  if (str_len*F(log)(base)/(mrb_float)0.69314718055994530942
      < MRB_BIGNUM_BIT*MRB_BIGNUM_MUL_RECURSION_CUTOFF) {
    return bn_from_str_basic(mrb, str, str_len, base);
  }

  /* Convert upper and lower halves */
  divisor = bn_find_divisor(divisors, str_len);
  split = divisor->power;
  mul = divisor->divisor;
  lnum = bn_from_str_recursive(mrb, str, str_len - split, base, divisors);
  rnum = bn_from_str_recursive(mrb, str + str_len - split, split, base, divisors);
  prod = bn_mul(mrb, lnum, mul);
  num = bn_add(mrb, prod, rnum, FALSE);
  bn_free(mrb, lnum);
  bn_free(mrb, rnum);
  bn_free(mrb, prod);

  return num;
}
#endif /* MRB_BIGNUM_ENABLE_RECURSION */

/* Convert a string to a Bignum using the given base */
/* The caller must ensure that the base is valid (0 or 2..36) */
static struct Bignum *
bn_from_str(mrb_state *mrb, char const *str, size_t str_len, unsigned base)
{
  char *str2;
  size_t i, j, str2_len;
  unsigned bits;
  struct Bignum *num;
  mrb_bool negative = FALSE;

  /* Skip leading whitespace */
  while (str_len != 0 && isspace(str[0])) {
    ++str;
    --str_len;
  }

  /* Interpret the sign if present */
  if (str_len != 0 && (str[0] == '+' || str[0] == '-')) {
    negative = str[0] == '-';
    ++str;
    --str_len;
  }

  /* Interpret the prefix if present */
  if (str_len >= 2 && str[0] == '0') {
    unsigned pbase = 0;
    switch (str[1]) {
    case 'x': case 'X':
      pbase = 16;
      break;
    case 'b': case 'B':
      pbase = 2;
      break;
    case 'o': case 'O':
      pbase = 8;
      break;
    case 'd': case 'D':
      pbase = 10;
      break;
    }
    if (pbase != 0) {
      base = pbase;
      str += 2;
      str_len -= 2;
    }
  }
  if (base == 0 && str_len >= 1 && str[0] == '0') {
    base = 8;
    ++str;
    --str_len;
  }

  /* Reduce the string to valid digits only */
  str2 = mrb_malloc(mrb, str_len);
  j = 0;
  for (i = 0; i < str_len; ++i) {
    char const *p;
    unsigned d;
    if (str[i] == '_') {
      continue;
    }
    p = strchr(mrb_digitmap, tolower(str[i]));
    if (p == NULL) {
      break;
    }
    d = (unsigned)(p - mrb_digitmap);
    if (d >= base) {
      break;
    }
    str2[j++] = str[i];
  }
  str2_len = j;

  /* Select the conversion algorithm */
  for (bits = 1; (1 << bits) < base; ++bits) {}
  if ((1 << bits) == base) {
    /* O(n) conversion for a base that is a power of two */
    num = bn_from_str_pow2(mrb, str2, str2_len, bits);
  }
  else {
    /* General conversion algorithm */
#ifdef MRB_BIGNUM_ENABLE_RECURSION
    {
      struct BignumDivisor *divisors;
      divisors = bn_compute_divisors(mrb, str2_len, base);
      num = bn_from_str_recursive(mrb, str2, str2_len, base, divisors);
      bn_free_divisors(mrb, divisors);
    }
#else
    num = bn_from_str_basic(mrb, str2, str2_len, base);
#endif
  }

  mrb_free(mrb, str2);
  num->negative = negative;
  return bn_normalize(num);
}

/* ------------------------------------------------------------------------*/
/* "<=>" */
/* ------------------------------------------------------------------------*/

/* Use when the right hand side is not Integer or Float */
static mrb_value
cmp_coerce(mrb_state *mrb, mrb_value self, mrb_value other)
{
  mrb_value v;

  if (!mrb_respond_to(mrb, other, mrb_intern_lit(mrb, "coerce"))) {
    mrb_raise(mrb, E_ARGUMENT_ERROR, "float expected");
  }

  v = mrb_funcall(mrb, other, "coerce", 1, self);
  if (mrb_array_p(v) && RARRAY_LEN(v) >= 2) {
    mrb_value f = mrb_ary_entry(v, 0);
    mrb_value s = mrb_ary_entry(v, 1);
    return mrb_funcall(mrb, f, "<=>", 1, s);
  }
  else {
    return mrb_nil_value();
  }
}

/* Fixnum <=> Bignum */
static int
cmp_fix_big(mrb_state *mrb, mrb_int left, mrb_value right)
{
  struct Bignum *bigself = fixnum_to_bignum(mrb, left);
  int cmp = bn_cmp(bigself, DATA_PTR(right));
  bn_free(mrb, bigself);
  return cmp;
}

/* Fixnum <=> Float */
static int
cmp_fix_flt(mrb_state *mrb, mrb_int left, mrb_float right)
{
  if (left < right) {
    return -1;
  }
  else if (left > right) {
    return +1;
  }
  else {
    return 0;
  }
}

/* Bignum <=> Float */
static int
cmp_big_flt(mrb_state *mrb, mrb_value left, mrb_float right)
{
  struct Bignum *bigright;
  mrb_float intpart, fracpart;
  int cmp;

  if (isinf(right)) {
    return signbit(right) ? +1 : -1;
  }

  fracpart = F(modf)(right, &intpart);
  /* Compare intpart to left */
  bigright = float_to_bignum(mrb, intpart);
  cmp = bn_cmp(DATA_PTR(left), bigright);
  bn_free(mrb, bigright);
  if (cmp == 0 && fracpart != 0) {
    /* intpart is equal, but right has a fractional part */
    if (fracpart < 0) {
      cmp = -1;
    }
    else {
      cmp = +1;
    }
  }
  return cmp;
}

/* 15.2.8.3.1  Fixnum#<=> */
static mrb_value
fixnum_cmp(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  int cmp;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum <=> Fixnum */
    {
      mrb_int fixother = mrb_fixnum(other);
      if (fixself < fixother) {
        cmp = -1;
      }
      else if (fixself > fixother) {
        cmp = +1;
      }
      else {
        cmp = 0;
      }
    }
    break;
  case num_bignum:
    /* Fixnum <=> Bignum */
    cmp = +cmp_fix_big(mrb, fixself, other);
    break;
  default:
    return cmp_coerce(mrb, self, other);
  }

  return mrb_fixnum_value(cmp);
}

/* 15.2.8.3.1  Bignum#<=> */
static mrb_value
bignum_cmp(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  int cmp;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum <=> Fixnum */
    cmp = -cmp_fix_big(mrb, mrb_fixnum(other), self);
    break;
  case num_bignum:
    /* Bignum <=> Bignum */
    cmp = bn_cmp(DATA_PTR(self), DATA_PTR(other));
    break;
  default:
    return cmp_coerce(mrb, self, other);
  }

  return mrb_fixnum_value(cmp);
}

/* 15.2.8.3.1  Float#<=> */
static mrb_value
float_cmp(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  int cmp;

  if (isnan(fltself)) {
    return mrb_nil_value();
  }

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float <=> Fixnum */
    {
      mrb_float fixother = mrb_fixnum(other);
      cmp = -cmp_fix_flt(mrb, fixother, fltself);
    }
    break;
  case num_bignum:
    /* Float <=> Bignum */
    cmp = -cmp_big_flt(mrb, other, fltself);
    break;
  case num_float:
    /* Float <=> Float */
    {
      mrb_float fltother = mrb_float(other);
      if (isnan(fltother)) {
        return mrb_nil_value();
      }
      if (fltself < fltother) {
        cmp = -1;
      }
      else if (fltself > fltother) {
        cmp = +1;
      }
      else {
        cmp = 0;
      }
    }
    break;
  default:
    return cmp_coerce(mrb, self, other);
  }

  return mrb_fixnum_value(cmp);
}

/* ------------------------------------------------------------------------*/
/* "==" */
/* ------------------------------------------------------------------------*/

/* Bignum == Float */
static mrb_bool
big_flt_eq(mrb_state *mrb, mrb_value self, mrb_float other)
{
  struct Bignum *bigother;
  mrb_bool eq;

  if (!isfinite(other)) {
    return 0;
  }
  bigother = float_to_bignum(mrb, other);
  eq = bn_cmp(DATA_PTR(self), bigother) == 0;
  bn_free(mrb, bigother);
  return eq;
}

/* Bignum == Fixnum */
static mrb_bool
big_fix_eq(mrb_state *mrb, mrb_value self, mrb_int other)
{
  struct Bignum *bigself = DATA_PTR(self);
  struct Bignum *bigother = fixnum_to_bignum(mrb, other);
  mrb_bool eq = bn_cmp(bigself, bigother) == 0;
  bn_free(mrb, bigother);
  return eq;
}

/* 15.2.8.3.2  Integer#== */
static mrb_value
fixnum_eq(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_bool eq;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum == Fixnum */
    eq = fixself == mrb_fixnum(other);
    break;
  case num_bignum:
    /* Fixnum == Bignum */
    eq = big_fix_eq(mrb, other, fixself);
    break;
  default:
    return mrb_funcall(mrb, other, "==", 1, self);
  }

  return mrb_bool_value(eq);
}

/* 15.2.8.3.2  Integer#== */
static mrb_value
bignum_eq(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_bool eq;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum == Fixnum */
    eq = big_fix_eq(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum == Bignum */
    eq = bn_cmp(DATA_PTR(self), DATA_PTR(other)) == 0;
    break;
  default:
    return mrb_funcall(mrb, other, "==", 1, self);
  }

  return mrb_bool_value(eq);
}

/* 15.2.9.3.2  Float#== */
static mrb_value
float_eq(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_bool eq;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float == Fixnum */
    eq = fltself == mrb_fixnum(other);
    break;
  case num_bignum:
    /* Float == Bignum */
    eq = big_flt_eq(mrb, other, fltself);
    break;
  case num_float:
    /* Float == Float */
    eq = fltself == mrb_float(other);
    break;
  default:
    return mrb_funcall(mrb, other, "==", 1, self);
  }

  return mrb_bool_value(eq);
}

/* ------------------------------------------------------------------------*/
/* "+" */
/* ------------------------------------------------------------------------*/

/* Fixnum + Fixnum */
static mrb_value
fix_fix_plus(mrb_state *mrb, mrb_int x, mrb_int y, mrb_bool subtract)
{
  mrb_bool sx, sy;
  mrb_uint ux, uy;
  mrb_bool ssum;
  mrb_uint usum;
  mrb_value sum;

#ifndef MRB_WORD_BOXING
  /* Because overflow in signed arithmetic invokes undefined behavior, the
     signed arithmetic is converted to unsigned.  This has the added effect
     of avoiding overflow altogether, except in one single corner case; and
     even that does not occur if word boxing is enabled, because that narrows
     Fixnum by one bit without changing the mrb_uint type. */
  if (!subtract && x == MRB_INT_MIN && y == MRB_INT_MIN) {
    struct Bignum *bsum = bn_alloc(mrb, FIXNUM_DIGITS + 1);
    bsum->digits[FIXNUM_DIGITS] = 1;
    bsum->negative = TRUE;
    return new_bignum(mrb, bsum, TRUE);
  }
#endif

  sx = x < 0;
  ux = x < 0 ? -(mrb_uint)x : +(mrb_uint)x;
  sy = (y < 0) ^ (subtract != 0);
  uy = y < 0 ? -(mrb_uint)y : +(mrb_uint)y;
  if (sx == sy) {
    /* Add */
    ssum = sx;
    usum = ux + uy;
  }
  else {
    /* Subtract */
    if (ux >= uy) {
      ssum = sx;
      usum = ux - uy;
    }
    else {
      ssum = sy;
      usum = uy - ux;
    }
  }
  /* Propagate carry */
  if (( ssum && usum > (mrb_uint)MRB_INT_MAX+1)
  ||  (!ssum && usum > (mrb_uint)MRB_INT_MAX+0)) {
    /* Overflow; return a Bignum */
    struct Bignum *bsum = bn_alloc(mrb, FIXNUM_DIGITS);
    bsum->negative = ssum;
#if FIXNUM_DIGITS == 1
    bsum->digits[0] = (bn_digit)usum;
#else
    {
      size_t i;
      for (i = 0; i < FIXNUM_DIGITS; ++i) {
        bsum->digits[i] = (bn_digit)usum;
        usum >>= MRB_BIGNUM_BIT;
      }
    }
#endif
    sum = new_bignum(mrb, bsum, TRUE);
  }
  else {
    /* Return a Fixnum */
    sum = mrb_fixnum_value((mrb_int)(ssum ? -usum : +usum));
  }

  return sum;
}

/* Fixnum + Bignum */
static mrb_value
fix_big_plus(mrb_state *mrb, mrb_int x, mrb_value y, mrb_bool subtract)
{
  struct Bignum *bigx = fixnum_to_bignum(mrb, x);
  struct Bignum *sum = bn_add(mrb, bigx, DATA_PTR(y), subtract);
  mrb_value out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  bn_free(mrb, bigx);
  return out;
}

/* Bignum + Fixnum */
static mrb_value
big_fix_plus(mrb_state *mrb, mrb_value x, mrb_int y, mrb_bool subtract)
{
  struct Bignum *bigy = fixnum_to_bignum(mrb, y);
  struct Bignum *sum = bn_add(mrb, DATA_PTR(x), bigy, subtract);
  mrb_value out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  bn_free(mrb, bigy);
  return out;
}

/* Bignum + Bignum */
static mrb_value
big_big_plus(mrb_state *mrb, mrb_value x, mrb_value y, mrb_bool subtract)
{
  struct Bignum *sum = bn_add(mrb, DATA_PTR(x), DATA_PTR(y), subtract);

  return new_bignum(mrb, sum, FIXNUM_CONVERT);
}

/* Coerce operands when the right side is not Integer or Float */
static mrb_value
op_coerce(mrb_state *mrb, mrb_value x, mrb_value y, char const *op)
{
  mrb_value v;

  if (!mrb_respond_to(mrb, y, mrb_intern_lit(mrb, "coerce"))) {
    mrb_raise(mrb, E_TYPE_ERROR, "expected Numeric");
  }

  v = mrb_funcall(mrb, y, "coerce", 1, x);
  if (mrb_array_p(v) && RARRAY_LEN(v) >= 2) {
    mrb_value f = mrb_ary_entry(v, 0);
    mrb_value s = mrb_ary_entry(v, 1);
    return mrb_funcall(mrb, f, op, 1, s);
  }
  else {
    mrb_raise(mrb, E_TYPE_ERROR, "expected Numeric");
    return mrb_nil_value();
  }
}

/* 15.2.8.3.3  Integer#+ */
static mrb_value
fixnum_plus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum + Fixnum */
    out = fix_fix_plus(mrb, fixself, mrb_fixnum(other), FALSE);
    break;
  case num_bignum:
    /* Fixnum + Bignum */
    out = fix_big_plus(mrb, fixself, other, FALSE);
    break;
  case num_float:
    /* Fixnum + Float */
    out = mrb_float_value(mrb, fixself + mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "+");
    break;
  }

  return out;
}

/* 15.2.8.3.3  Integer#+ */
static mrb_value
bignum_plus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum + Fixnum */
    out = big_fix_plus(mrb, self, mrb_fixnum(other), FALSE);
    break;
  case num_bignum:
    /* Bignum + Bignum */
    out = big_big_plus(mrb, self, other, FALSE);
    break;
  case num_float:
    /* Bignum + Float */
    out = mrb_float_value(mrb, bn_to_float(DATA_PTR(self)) + mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "+");
    break;
  }

  return out;
}

/* 15.2.9.3.3  Float#+ */
static mrb_value
float_plus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float + Fixnum */
    out = mrb_float_value(mrb, fltself + mrb_fixnum(other));
    break;
  case num_bignum:
    /* Float + Bignum */
    out = mrb_float_value(mrb, fltself + bn_to_float(DATA_PTR(other)));
    break;
  case num_float:
    /* Float + Float */
    out = mrb_float_value(mrb, fltself + mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "+");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "-" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.4  Integer#- */
static mrb_value
fixnum_minus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum - Fixnum */
    out = fix_fix_plus(mrb, fixself, mrb_fixnum(other), TRUE);
    break;
  case num_bignum:
    /* Fixnum - Bignum */
    out = fix_big_plus(mrb, fixself, other, TRUE);
    break;
  case num_float:
    /* Fixnum - Float */
    out = mrb_float_value(mrb, fixself - mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "-");
    break;
  }

  return out;
}

/* 15.2.8.3.4  Integer#- */
static mrb_value
bignum_minus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum - Fixnum */
    out = big_fix_plus(mrb, self, mrb_fixnum(other), TRUE);
    break;
  case num_bignum:
    /* Bignum - Bignum */
    out = big_big_plus(mrb, self, other, TRUE);
    break;
  case num_float:
    /* Bignum - Float */
    out = mrb_float_value(mrb, bn_to_float(DATA_PTR(self)) - mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "-");
    break;
  }

  return out;
}

/* 15.2.9.3.4  Float#- */
static mrb_value
float_minus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float - Fixnum */
    out = mrb_float_value(mrb, fltself - mrb_fixnum(other));
    break;
  case num_bignum:
    /* Float - Bignum */
    out = mrb_float_value(mrb, fltself - bn_to_float(DATA_PTR(other)));
    break;
  case num_float:
    /* Float - Float */
    out = mrb_float_value(mrb, fltself - mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "-");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "*" */
/* ------------------------------------------------------------------------*/

/* Fixnum * Fixnum */
static mrb_value
fix_fix_mul(mrb_state *mrb, mrb_int x, mrb_int y)
{
  /* Fixnums with absolute value not exceeding mul_max never overflow when
     multiplied */
#ifdef MRB_WORD_BOXING
#  if MRB_INT_BIT == 32
  static const mrb_int mul_max = 32767;
#  else
  static const mrb_int mul_max = 2147483647;
#  endif
#else
#  if MRB_INT_BIT == 16
  static const mrb_int mul_max = 181;
#  elif MRB_INT_BIT == 32
  static const mrb_int mul_max = 46340;
#  else
  static const mrb_int mul_max = 3037000499;
#  endif
#endif

  struct Bignum *bigx, *bigy, *out;

  if (-mul_max <= x && x <= +mul_max
  &&  -mul_max <= y && y <= +mul_max) {
    /* Small number optimization; product will never overflow */
    return mrb_fixnum_value(x * y);
  }

  bigx = fixnum_to_bignum(mrb, x);
  bigy = fixnum_to_bignum(mrb, y);
  out = bn_mul(mrb, bigx, bigy);
  bn_free(mrb, bigx);
  bn_free(mrb, bigy);

  return new_bignum(mrb, out, TRUE);
}

/* Fixnum * Bignum */
static mrb_value
fix_big_mul(mrb_state *mrb, mrb_int x, mrb_value y)
{
  struct Bignum *bigx = fixnum_to_bignum(mrb, x);
  struct Bignum *out = bn_mul(mrb, bigx, DATA_PTR(y));

  bn_free(mrb, bigx);
  return new_bignum(mrb, out, FIXNUM_CONVERT);
}

/* Bignum * Bignum */
static mrb_value
big_big_mul(mrb_state *mrb, mrb_value x, mrb_value y)
{
  struct Bignum *sum = bn_mul(mrb, DATA_PTR(x), DATA_PTR(y));

  return new_bignum(mrb, sum, FIXNUM_CONVERT);
}

/* 15.2.8.3.5  Integer#* */
static mrb_value
fixnum_mul(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum * Fixnum */
    out = fix_fix_mul(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum * Bignum */
    out = fix_big_mul(mrb, fixself, other);
    break;
  case num_float:
    /* Fixnum * Float */
    out = mrb_float_value(mrb, fixself * mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "*");
    break;
  }

  return out;
}

/* 15.2.8.3.5  Integer#* */
static mrb_value
bignum_mul(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum * Fixnum */
    out = fix_big_mul(mrb, mrb_fixnum(other), self);
    break;
  case num_bignum:
    /* Bignum * Bignum */
    out = big_big_mul(mrb, self, other);
    break;
  case num_float:
    /* Bignum * Float */
    out = mrb_float_value(mrb, bn_to_float(DATA_PTR(self)) * mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "*");
    break;
  }

  return out;
}

/* 15.2.9.3.5  Float#* */
static mrb_value
float_mul(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float * Fixnum */
    out = mrb_float_value(mrb, fltself * mrb_fixnum(other));
    break;
  case num_bignum:
    /* Float * Bignum */
    out = mrb_float_value(mrb, fltself * bn_to_float(DATA_PTR(other)));
    break;
  case num_float:
    /* Float * Float */
    out = mrb_float_value(mrb, fltself * mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "*");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "/" */
/* ------------------------------------------------------------------------*/

/* Fixnum / Fixnum */
static mrb_value
fix_fix_div(mrb_state *mrb, mrb_int x, mrb_int y)
{
  mrb_int quo;

  if (y == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  /* This is the only way that division of Fixnums can overflow */
  if (x == MRB_INT_MIN && y == -1) {
    struct Bignum *out = fixnum_to_bignum(mrb, x);
    out->negative = FALSE;
    return new_bignum(mrb, out, FALSE);
  }

  quo = x / y;
  if ((x >= 0) != (y >= 0) && x % y != 0) {
    --quo;
  }

  return mrb_fixnum_value(quo);
}

/* Fixnum / Bignum */
static mrb_value
fix_big_div(mrb_state *mrb, mrb_int self, mrb_value other)
{
  struct Bignum *bigself, *bigother, *out;

  bigother = DATA_PTR(other);
  if (bigother->len == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  bigself = fixnum_to_bignum(mrb, self);
  out = bn_div(mrb, bigself, bigother);
  bn_free(mrb, bigself);

  return new_bignum(mrb, out, FIXNUM_CONVERT);
}

/* Bignum / Fixnum */
static mrb_value
big_fix_div(mrb_state *mrb, mrb_value self, mrb_int other)
{
  struct Bignum *bigother, *out;

  if (other == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  bigother = fixnum_to_bignum(mrb, other);
  out = bn_div(mrb, DATA_PTR(self), bigother);
  bn_free(mrb, bigother);

  return new_bignum(mrb, out, FIXNUM_CONVERT);
}

/* Bignum / Bignum */
static mrb_value
big_big_div(mrb_state *mrb, mrb_value self, mrb_value other)
{
  struct Bignum *bigother;
  struct Bignum *sum;

  bigother = DATA_PTR(other);
  if (bigother->len == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  sum = bn_div(mrb, DATA_PTR(self), bigother);

  return new_bignum(mrb, sum, FIXNUM_CONVERT);
}

/* 15.2.8.3.6  Integer#/ */
static mrb_value
fixnum_div(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum / Fixnum */
    out = fix_fix_div(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum / Bignum */
    out = fix_big_div(mrb, fixself, other);
    break;
  default:
    out = op_coerce(mrb, self, other, "/");
    break;
  }

  return out;
}

/* 15.2.8.3.6  Integer#/ */
static mrb_value
bignum_div(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum / Fixnum */
    out = big_fix_div(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum / Bignum */
    out = big_big_div(mrb, self, other);
    break;
  default:
    out = op_coerce(mrb, self, other, "/");
    break;
  }

  return out;
}

/* 15.2.8.3.6  Integer#/ */
static mrb_value
float_div(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float / Fixnum */
    out = mrb_float_value(mrb, fltself / mrb_fixnum(other));
    break;
  case num_bignum:
    /* Float / Bignum */
    out = mrb_float_value(mrb, fltself / bn_to_float(DATA_PTR(other)));
    break;
  case num_float:
    /* Float / Float */
    out = mrb_float_value(mrb, fltself / mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "/");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "%" */
/* ------------------------------------------------------------------------*/

/* Fixnum % Fixnum */
static mrb_value
fix_fix_mod(mrb_state *mrb, mrb_int x, mrb_int y)
{
  mrb_int rem;

  if (y == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  rem = x % y;
  if ((x >= 0) != (y >= 0) && rem != 0) {
    rem += y;
  }

  return mrb_fixnum_value(rem);
}

/* Fixnum % Bignum */
static mrb_value
fix_big_mod(mrb_state *mrb, mrb_int self, mrb_value other)
{
  struct Bignum *bigself, *bigother, *out;

  bigother = DATA_PTR(other);
  if (bigother->len == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  bigself = fixnum_to_bignum(mrb, self);
  out = bn_mod(mrb, bigself, bigother);
  bn_free(mrb, bigself);

  return new_bignum(mrb, out, FIXNUM_CONVERT);
}

/* Bignum % Fixnum */
static mrb_value
big_fix_mod(mrb_state *mrb, mrb_value self, mrb_int other)
{
  struct Bignum *bigother, *out;

  if (other == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  bigother = fixnum_to_bignum(mrb, other);
  out = bn_mod(mrb, DATA_PTR(self), bigother);
  bn_free(mrb, bigother);

  return new_bignum(mrb, out, FIXNUM_CONVERT);
}

/* Bignum % Bignum */
static mrb_value
big_big_mod(mrb_state *mrb, mrb_value self, mrb_value other)
{
  struct Bignum *bigother, *sum;

  bigother = DATA_PTR(other);
  if (bigother->len == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  sum = bn_mod(mrb, DATA_PTR(self), bigother);

  return new_bignum(mrb, sum, FIXNUM_CONVERT);
}

/* 15.2.8.3.7  Integer#% */
static mrb_value
fixnum_mod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum % Fixnum */
    out = fix_fix_mod(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum % Bignum */
    out = fix_big_mod(mrb, fixself, other);
    break;
  default:
    out = op_coerce(mrb, self, other, "%");
    break;
  }

  return out;
}

/* 15.2.8.3.7  Integer#% */
static mrb_value
bignum_mod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum % Fixnum */
    out = big_fix_mod(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum % Bignum */
    out = big_big_mod(mrb, self, other);
    break;
  default:
    out = op_coerce(mrb, self, other, "%");
    break;
  }

  return out;
}

/* 15.2.9.3.7  Float#% */
static mrb_value
float_mod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float % Fixnum */
    out = mrb_float_value(mrb, F(fmod)(fltself, mrb_fixnum(other)));
    break;
  case num_bignum:
    /* Float % Bignum */
    out = mrb_float_value(mrb, F(fmod)(fltself, bn_to_float(DATA_PTR(other))));
    break;
  case num_float:
    /* Float % Float */
    out = mrb_float_value(mrb, F(fmod)(fltself, mrb_float(other)));
    break;
  default:
    out = op_coerce(mrb, self, other, "%");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "divmod" */
/* ------------------------------------------------------------------------*/

/* Fixnum.divmod(Fixnum) */
static mrb_value
fix_fix_divmod(mrb_state *mrb, mrb_int x, mrb_int y)
{
  mrb_value out[2];

  if (y == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  if (x == MRB_INT_MIN && y == -1) {
    /* Fixnum division overflows */
    struct Bignum *q = fixnum_to_bignum(mrb, x);
    q->negative = FALSE;
    out[0] = new_bignum(mrb, q, FALSE);
    out[1] = mrb_fixnum_value(0);
  }
  else {
    mrb_int q = x / y;
    mrb_int r = x % y;
    /* Division rounds down */
    if (q < 0 && r != 0) {
      --q;
      r += y;
    }
    out[0] = mrb_fixnum_value(q);
    out[1] = mrb_fixnum_value(r);
  }

  return mrb_ary_new_from_values(mrb, 2, out);
}

/* Float.divmod(Float) */
static mrb_value
flt_flt_divmod(mrb_state *mrb, mrb_float x, mrb_float y)
{
  mrb_float q, r;
  mrb_value out[2];

  q = F(floor)(x/y);
  r = x - q*y;

  out[0] = mrb_float_value(mrb, q);
  out[1] = mrb_float_value(mrb, r);

  return mrb_ary_new_from_values(mrb, 2, out);
}

/* Bignum.divmod(Bignum) */
static mrb_value
big_big_divmod(mrb_state *mrb, struct Bignum const *x, struct Bignum const *y)
{
  struct Bignum *q, *r;
  mrb_value out[2];

  bn_divmod(mrb, &q, &r, x, y);

  out[0] = new_bignum(mrb, q, FIXNUM_CONVERT);
  out[1] = new_bignum(mrb, r, FIXNUM_CONVERT);

  return mrb_ary_new_from_values(mrb, 2, out);
}

/* Fixnum.divmod(Bignum) */
static mrb_value
fix_big_divmod(mrb_state *mrb, mrb_int x, struct Bignum const *y)
{
  struct Bignum *bigx = fixnum_to_bignum(mrb, x);
  mrb_value out = big_big_divmod(mrb, bigx, y);
  bn_free(mrb, bigx);
  return out;
}

/* Bignum.divmod(Fixnum) */
static mrb_value
big_fix_divmod(mrb_state *mrb, struct Bignum const *x, mrb_int y)
{
  struct Bignum *bigy = fixnum_to_bignum(mrb, y);
  mrb_value out = big_big_divmod(mrb, x, bigy);
  bn_free(mrb, bigy);
  return out;
}

/* Fixnum#divmod */
static mrb_value
fixnum_divmod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum.divmod(Fixnum) */
    out = fix_fix_divmod(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum.divmod(Bignum) */
    out = fix_big_divmod(mrb, fixself, DATA_PTR(other));
    break;
  case num_float:
    /* Fixnum.divmod(Float) */
    out = flt_flt_divmod(mrb, fixself, mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "divmod");
    break;
  }

  return out;
}

/* Bignum#divmod */
static mrb_value
bignum_divmod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum.divmod(Fixnum) */
    out = big_fix_divmod(mrb, DATA_PTR(self), mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum.divmod(Bignum) */
    out = big_big_divmod(mrb, DATA_PTR(self), DATA_PTR(other));
    break;
  case num_float:
    /* Bignum.divmod(Float) */
    out = flt_flt_divmod(mrb, bn_to_float(DATA_PTR(self)), mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "divmod");
    break;
  }

  return out;
}

/* Float#divmod */
static mrb_value
float_divmod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float.divmod(Fixnum) */
    out = flt_flt_divmod(mrb, fltself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Float.divmod(Bignum) */
    out = flt_flt_divmod(mrb, fltself, bn_to_float(DATA_PTR(other)));
    break;
  case num_float:
    /* Float.divmod(Float) */
    out = flt_flt_divmod(mrb, fltself, mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "divmod");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "quo" */
/* ------------------------------------------------------------------------*/

/* The CRuby documentation describes quo as returning the "most exact division
   (rational for integers, float for floats).  Because this gem does not
   implement rationals, quo always returns a float. */

static mrb_value
quo(mrb_state *mrb, mrb_value self, mrb_float fltself)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Numeric.quo(Fixnum) */
    out = mrb_float_value(mrb, fltself / mrb_fixnum(other));
    break;
  case num_bignum:
    /* Numeric.quo(Bignum) */
    out = mrb_float_value(mrb, fltself / bn_to_float(DATA_PTR(other)));
    break;
  case num_float:
    /* Numeric.quo(Float) */
    out = mrb_float_value(mrb, fltself / mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "quo");
    break;
  }

  return out;
}

/* Fixnum#quo */
static mrb_value
fixnum_quo(mrb_state *mrb, mrb_value self)
{
  return quo(mrb, self, mrb_fixnum(self));
}

/* Bignum#quo */
static mrb_value
bignum_quo(mrb_state *mrb, mrb_value self)
{
  return quo(mrb, self, bn_to_float(DATA_PTR(self)));
}

/* Float#quo */
static mrb_value
float_quo(mrb_state *mrb, mrb_value self)
{
  return quo(mrb, self, mrb_float(self));
}

/* ------------------------------------------------------------------------*/
/* "**" */
/* ------------------------------------------------------------------------*/

static mrb_value
big_fix_pow(mrb_state *mrb, struct Bignum const *x, int64_t y, mrb_bool fixnum_conv)
{
  struct Bignum *z;

  if (y < 0) {
    return mrb_float_value(mrb, F(pow)(bn_to_float(x), y));
  }

  z = bn_pow(mrb, x, y);
  return new_bignum(mrb, z, fixnum_conv);
}

static mrb_value
fix_fix_pow(mrb_state *mrb, mrb_int x, mrb_int y)
{
  struct Bignum *bigx = fixnum_to_bignum(mrb, x);
  mrb_value z = big_fix_pow(mrb, bigx, y, TRUE);
  bn_free(mrb, bigx);
  return z;
}

static mrb_value
big_big_pow(mrb_state *mrb, struct Bignum const *x, struct Bignum const *y, mrb_bool fixnum_conv)
{
  mrb_value z;

  if (y->negative) {
    z = mrb_float_value(mrb, F(pow)(bn_to_float(x), bn_to_float(y)));
  }
  else {
    int64_t fixy = bignum_to_int64(y);
    if (fixy == INT64_MIN) {
      mrb_raise(mrb, E_RANGE_ERROR, "exponent too big");
    }
    z = big_fix_pow(mrb, x, fixy, fixnum_conv);
  }
  return z;
}

static mrb_value
fix_big_pow(mrb_state *mrb, mrb_int x, struct Bignum const *y)
{
  struct Bignum *bigx = fixnum_to_bignum(mrb, x);
  mrb_value z = big_big_pow(mrb, bigx, y, TRUE);
  bn_free(mrb, bigx);
  return z;
}

/* Fixnum#** */
static mrb_value
fixnum_pow(mrb_state *mrb, mrb_value self)
{
  mrb_int fixself = mrb_fixnum(self);
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum ** Fixnum */
    out = fix_fix_pow(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum ** Bignum */
    out = fix_big_pow(mrb, fixself, DATA_PTR(other));
    break;
  case num_float:
    /* Fixnum ** Float */
    out = mrb_float_value(mrb, F(pow)(fixself, mrb_float(other)));
    break;
  default:
    out = op_coerce(mrb, self, other, "**");
    break;
  }

  return out;
}

/* Bignum#** */
static mrb_value
bignum_pow(mrb_state *mrb, mrb_value self)
{
  struct Bignum *bigself = DATA_PTR(self);
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum ** Fixnum */
    out = big_fix_pow(mrb, bigself, mrb_fixnum(other), FIXNUM_CONVERT);
    break;
  case num_bignum:
    /* Bignum ** Bignum */
    out = big_big_pow(mrb, bigself, DATA_PTR(other), FIXNUM_CONVERT);
    break;
  case num_float:
    /* Bignum ** Float */
    out = mrb_float_value(mrb, F(pow)(bn_to_float(bigself), mrb_float(other)));
    break;
  default:
    out = op_coerce(mrb, self, other, "**");
    break;
  }

  return out;
}

/* Float#** */
static mrb_value
float_pow(mrb_state *mrb, mrb_value self)
{
  mrb_float fltself = mrb_float(self);
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float ** Fixnum */
    out = mrb_float_value(mrb, F(pow)(fltself, mrb_fixnum(other)));
    break;
  case num_bignum:
    /* Float ** Bignum */
    out = mrb_float_value(mrb, F(pow)(fltself, bn_to_float(DATA_PTR(other))));
    break;
  case num_float:
    /* Float ** Float */
    out = mrb_float_value(mrb, F(pow)(fltself, mrb_float(other)));
    break;
  default:
    out = op_coerce(mrb, self, other, "**");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "~" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.8  Integer#~ */
static mrb_value
bignum_rev(mrb_state *mrb, mrb_value self)
{
  /* Implemented as -self - 1 */
  static const bn_digit one = 1;
  struct Bignum *in1 = DATA_PTR(self);
  struct Bignum *out = bn_alloc(mrb, in1->len + 1);
  if (in1->negative) {
    bn_sub_basic(out->digits, in1->digits, in1->len, &one, 1);
  }
  else {
    out->digits[in1->len] = bn_add_basic(
            out->digits, in1->digits, in1->len, &one, 1);
  }
  out->negative = !in1->negative;

  return new_bignum(mrb, out, FIXNUM_CONVERT);
}

/* ------------------------------------------------------------------------*/
/* "&" */
/* ------------------------------------------------------------------------*/

static mrb_value
bitwise_coerce(mrb_state *mrb, mrb_value x, mrb_value y, char const *op)
{
  if (mrb_respond_to(mrb, y, mrb_intern_lit(mrb, "coerce"))) {
    mrb_value v;
    v = mrb_funcall(mrb, y, "coerce", 1, x);
    if (mrb_array_p(v) && RARRAY_LEN(v) >= 2) {
      mrb_value f = mrb_ary_entry(v, 0);
      mrb_value s = mrb_ary_entry(v, 1);
      struct RClass *integer = mrb_class_get(mrb, "Integer");
      if (mrb_obj_is_kind_of(mrb, f, integer)
      &&  mrb_obj_is_kind_of(mrb, s, integer)) {
        return mrb_funcall(mrb, f, op, 1, s);
      }
    }
  }

  mrb_raise(mrb, E_TYPE_ERROR, "bitwise arithmetic requires Integer");
  return mrb_nil_value();
}

/* Fixnum & Bignum */
static mrb_value
fix_big_and(mrb_state *mrb, mrb_int x, mrb_value y)
{
  struct Bignum *bigx = fixnum_to_bignum(mrb, x);
  struct Bignum *sum = bn_and(mrb, bigx, DATA_PTR(y));

  bn_free(mrb, bigx);
  return new_bignum(mrb, sum, FIXNUM_CONVERT);
}

/* Bignum & Bignum */
static mrb_value
big_big_and(mrb_state *mrb, mrb_value x, mrb_value y)
{
  struct Bignum *sum = bn_and(mrb, DATA_PTR(x), DATA_PTR(y));

  return new_bignum(mrb, sum, FIXNUM_CONVERT);
}

/* 15.2.8.3.9  Integer#& */
static mrb_value
fixnum_and(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum & Fixnum */
    out = mrb_fixnum_value(fixself & mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum & Bignum */
    out = fix_big_and(mrb, fixself, other);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "&");
    break;
  }

  return out;
}

/* 15.2.8.3.9  Integer#& */
static mrb_value
bignum_and(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum & Fixnum */
    out = fix_big_and(mrb, mrb_fixnum(other), self);
    break;
  case num_bignum:
    /* Bignum & Bignum */
    out = big_big_and(mrb, self, other);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "&");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "|" */
/* ------------------------------------------------------------------------*/

/* Fixnum | Bignum */
static mrb_value
fix_big_or(mrb_state *mrb, mrb_int x, mrb_value y)
{
  struct Bignum *bigx = fixnum_to_bignum(mrb, x);
  struct Bignum *sum = bn_or(mrb, bigx, DATA_PTR(y));

  bn_free(mrb, bigx);
  return new_bignum(mrb, sum, FIXNUM_CONVERT);
}

/* Bignum | Bignum */
static mrb_value
big_big_or(mrb_state *mrb, mrb_value x, mrb_value y)
{
  struct Bignum *sum = bn_or(mrb, DATA_PTR(x), DATA_PTR(y));

  return new_bignum(mrb, sum, FIXNUM_CONVERT);
}

/* 15.2.8.3.10 Integer#| */
static mrb_value
fixnum_or(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum | Fixnum */
    out = mrb_fixnum_value(fixself | mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum | Bignum */
    out = fix_big_or(mrb, fixself, other);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "|");
    break;
  }

  return out;
}

/* 15.2.8.3.10 Integer#| */
static mrb_value
bignum_or(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum | Fixnum */
    out = fix_big_or(mrb, mrb_fixnum(other), self);
    break;
  case num_bignum:
    /* Bignum | Bignum */
    out = big_big_or(mrb, self, other);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "|");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "^" */
/* ------------------------------------------------------------------------*/

/* Fixnum ^ Bignum */
static mrb_value
fix_big_xor(mrb_state *mrb, mrb_int x, mrb_value y)
{
  struct Bignum *bigx = fixnum_to_bignum(mrb, x);
  struct Bignum *sum = bn_xor(mrb, bigx, DATA_PTR(y));

  bn_free(mrb, bigx);
  return new_bignum(mrb, sum, FIXNUM_CONVERT);
}

/* Bignum ^ Bignum */
static mrb_value
big_big_xor(mrb_state *mrb, mrb_value x, mrb_value y)
{
  struct Bignum *sum = bn_xor(mrb, DATA_PTR(x), DATA_PTR(y));

  return new_bignum(mrb, sum, FIXNUM_CONVERT);
}

/* 15.2.8.3.11 Integer#^ */
static mrb_value
fixnum_xor(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum ^ Fixnum */
    out = mrb_fixnum_value(fixself ^ mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum ^ Bignum */
    out = fix_big_xor(mrb, fixself, other);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "^");
    break;
  }

  return out;
}

/* 15.2.8.3.11 Integer#^ */
static mrb_value
bignum_xor(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum ^ Fixnum */
    out = fix_big_xor(mrb, mrb_fixnum(other), self);
    break;
  case num_bignum:
    /* Bignum ^ Bignum */
    out = big_big_xor(mrb, self, other);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "^");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "<<" */
/* ------------------------------------------------------------------------*/

/* Optimized right shift for Fixnum (don't convert to Bignum) */
static mrb_value
fix_fix_rshift_u(mrb_state *mrb, mrb_int self, uint64_t other)
{
  /* Avoid undefined behavior */
  if (other >= MRB_INT_BIT) {
    return mrb_fixnum_value((self < 0) ? -1 : 0);
  }

  /* C does not specify whether signs are kept when a negative number is
     shifted right, so shift positive numbers only; also round division
     downward */
  if (self >= 0) {
    return mrb_fixnum_value(self >> other);
  }
  else {
    mrb_uint u1, u2;
    /* Compute as -(-self >> other) */
    u1 = -(mrb_uint)self;
    u2 = u1 >> other;
    if ((u2 << other) != u1) {
      ++u2;
    }
    return mrb_fixnum_value((mrb_int)-u2);
  }
}

/* Fixnum << Fixnum */
static mrb_value
fix_fix_lshift(mrb_state *mrb, mrb_int self, int64_t other)
{
  if (other < 0) {
    return fix_fix_rshift_u(mrb, self, -other);
  }
  else {
    struct Bignum *bigself = fixnum_to_bignum(mrb, self);
    struct Bignum *out = bn_lshift(mrb, bigself, other);

    bn_free(mrb, bigself);
    return new_bignum(mrb, out, TRUE);
  }
}

/* Bignum << Fixnum */
static mrb_value
big_fix_lshift(mrb_state *mrb, mrb_value self, int64_t other)
{
  struct Bignum *out = bn_lshift(mrb, DATA_PTR(self), other);

  return new_bignum(mrb, out, FIXNUM_CONVERT);
}

/* Result of right shift that is deemed too large */
static mrb_value
big_rshift_large(mrb_state *mrb, mrb_value self)
{
  struct Bignum *bigself = DATA_PTR(self);
  int result = bigself->negative ? -1 : 0;
#if FIXNUM_CONVERT
  return mrb_fixnum_value(result);
#else
  return new_bignum(mrb, fixnum_to_bignum(mrb, result), FALSE);
#endif
}

/* 15.2.8.3.12 Integer#<< */
static mrb_value
fixnum_lshift(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum << Fixnum */
    out = fix_fix_lshift(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum << Bignum */
    {
      struct Bignum *bigother = DATA_PTR(other);
      int64_t fixother = bignum_to_int64(bigother);
      if (fixother == INT64_MIN) {
        if (bigother->negative) {
          out = mrb_fixnum_value(fixself < 0 ? -1 : 0);
        }
        else {
          mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
          out = mrb_nil_value();
        }
      }
      else {
        out = fix_fix_lshift(mrb, fixself, fixother);
      }
    }
    break;
  case num_float:
    /* Fixnum << Float */
    {
      mrb_float fltother = mrb_float(other);
      if (fltother < INT64_MIN) {
        out = mrb_fixnum_value(fixself < 0 ? -1 : 0);
      }
      else if (fltother > INT64_MAX) {
        mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
        out = mrb_nil_value();
      }
      else {
        out = fix_fix_lshift(mrb, fixself, fltother);
      }
    }
    break;
  default:
    mrb_raise(mrb, E_TYPE_ERROR, "expected Integer");
    out = mrb_nil_value();
    break;
  }

  return out;
}

/* 15.2.8.3.12 Integer#<< */
static mrb_value
bignum_lshift(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum << Fixnum */
    out = big_fix_lshift(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum << Bignum */
    {
      struct Bignum *bigother = DATA_PTR(other);
      int64_t fixother = bignum_to_int64(bigother);
      if (fixother == INT64_MIN) {
        if (bigother->negative) {
          out = big_rshift_large(mrb, self);
        }
        else {
          mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
          out = mrb_nil_value();
        }
      }
      else {
        out = big_fix_lshift(mrb, self, fixother);
      }
    }
    break;
  case num_float:
    /* Fixnum << Float */
    {
      mrb_float fltother = mrb_float(other);
      if (fltother < INT64_MIN) {
        out = big_rshift_large(mrb, self);
      }
      else if (fltother > INT64_MAX) {
        mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
        out = mrb_nil_value();
      }
      else {
        out = big_fix_lshift(mrb, self, fltother);
      }
    }
    break;
  default:
    mrb_raise(mrb, E_TYPE_ERROR, "expected Integer");
    out = mrb_nil_value();
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* ">>" */
/* ------------------------------------------------------------------------*/

/* Fixnum >> Fixnum */
static mrb_value
fix_fix_rshift(mrb_state *mrb, mrb_int self, int64_t other)
{
  if (other >= 0) {
    return fix_fix_rshift_u(mrb, self, +other);
  }
  else {
    struct Bignum *bigself = fixnum_to_bignum(mrb, self);
    struct Bignum *out = bn_rshift(mrb, bigself, other);

    bn_free(mrb, bigself);
    return new_bignum(mrb, out, TRUE);
  }
}

/* Bignum >> Fixnum */
static mrb_value
big_fix_rshift(mrb_state *mrb, mrb_value self, int64_t other)
{
  struct Bignum *out = bn_rshift(mrb, DATA_PTR(self), other);

  return new_bignum(mrb, out, FIXNUM_CONVERT);
}

/* 15.2.8.3.13 Integer#>> */
static mrb_value
fixnum_rshift(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum >> Fixnum */
    out = fix_fix_rshift(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum >> Bignum */
    {
      struct Bignum *bigother = DATA_PTR(other);
      int64_t fixother = bignum_to_int64(bigother);
      if (fixother == INT64_MIN) {
        struct Bignum *bigother = DATA_PTR(other);
        if (!bigother->negative) {
          out = mrb_fixnum_value(fixself < 0 ? -1 : 0);
        }
        else {
          mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
          out = mrb_nil_value();
        }
      }
      else {
        out = fix_fix_rshift(mrb, fixself, fixother);
      }
    }
    break;
  case num_float:
    /* Fixnum >> Float */
    {
      mrb_float fltother = mrb_float(other);
      if (fltother > INT64_MAX) {
        out = mrb_fixnum_value(fixself < 0 ? -1 : 0);
      }
      else if (fltother < INT64_MIN) {
        mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
        out = mrb_nil_value();
      }
      else {
        out = fix_fix_rshift(mrb, fixself, fltother);
      }
    }
    break;
  default:
    mrb_raise(mrb, E_TYPE_ERROR, "expected Integer");
    out = mrb_nil_value();
    break;
  }

  return out;
}

/* 15.2.8.3.13 Integer#>> */
static mrb_value
bignum_rshift(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum >> Fixnum */
    out = big_fix_rshift(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum >> Bignum */
    {
      struct Bignum *bigother = DATA_PTR(other);
      int64_t fixother = bignum_to_int64(bigother);
      if (fixother == INT64_MIN) {
        struct Bignum *bigother = DATA_PTR(other);
        if (!bigother->negative) {
          out = big_rshift_large(mrb, self);
        }
        else {
          mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
          out = mrb_nil_value();
        }
      }
      else {
        out = big_fix_rshift(mrb, self, fixother);
      }
    }
    break;
  case num_float:
    /* Fixnum >> Float */
    {
      mrb_float fltother = mrb_float(other);
      if (fltother > INT64_MAX) {
        out = big_rshift_large(mrb, self);
      }
      else if (fltother < INT64_MIN) {
        mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
        out = mrb_nil_value();
      }
      else {
        out = big_fix_rshift(mrb, self, fltother);
      }
    }
    break;
  default:
    mrb_raise(mrb, E_TYPE_ERROR, "expected Integer");
    out = mrb_nil_value();
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "eql?" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.16 Integer#eql? */
static mrb_value
fixnum_eql(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_bool eql;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum.eql?(Fixnum) */
    eql = mrb_fixnum(self) == mrb_fixnum(other);
    break;
  case num_bignum:
    /* Fixnum.eql?(Bignum) */
    eql = big_fix_eq(mrb, other, mrb_fixnum(self));
    break;
  default:
    eql = FALSE;
    break;
  }

  return mrb_bool_value(eql);
}

/* 15.2.8.3.16 Integer#eql? */
static mrb_value
bignum_eql(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_bool eql;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum.eql?(Fixnum) */
    eql = big_fix_eq(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum.eql?(Bignum) */
    eql = bn_cmp(DATA_PTR(self), DATA_PTR(other)) == 0;
    break;
  default:
    eql = FALSE;
    break;
  }

  return mrb_bool_value(eql);
}

/* ------------------------------------------------------------------------*/
/* "hash" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.18 Integer#hash */
static mrb_value
bignum_hash(mrb_state *mrb, mrb_value self)
{
  struct Bignum *bigself = DATA_PTR(self);
  mrb_uint key = 0;
  size_t i, j;

  for (i = 0; i < bigself->len; ++i) {
    bn_digit digit = bigself->digits[i];
    for (j = 0; j < MRB_BIGNUM_BIT; j += 8) {
      key = key*65599 + (digit & 0xFF);
      digit >>= 8;
    }
  }

  return mrb_fixnum_value((mrb_int)(key + (key >> 5)));
}

/* ------------------------------------------------------------------------*/
/* "to_f" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.23 Integer#to_f */
static mrb_value
bignum_to_f(mrb_state *mrb, mrb_value self)
{
  struct Bignum *bigself = DATA_PTR(self);
  mrb_float fltself = bn_to_float(bigself);

  return mrb_float_value(mrb, fltself);
}

/* ------------------------------------------------------------------------*/
/* "to_s" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.25 Integer#to_s */
static mrb_value
bignum_to_s(mrb_state *mrb, mrb_value self)
{
  struct Bignum *bigself = DATA_PTR(self);
  mrb_int base = 10;
  char *str;
  mrb_value rstr;

  mrb_get_args(mrb, "|i", &base);

  if (base < 2 || 36 < base) {
    mrb_raisef(mrb, E_ARGUMENT_ERROR, "invalid radix %S", mrb_fixnum_value(base));
  }

  str = bn_to_str(mrb, bigself, base);
  rstr = mrb_str_new_cstr(mrb, str);
  bn_free(mrb, str);
  return rstr;
}

/* ------------------------------------------------------------------------*/
/* Float to Integer conversions */
/* ------------------------------------------------------------------------*/

/* 15.2.9.3.8 Float#ceil */
static mrb_value
float_ceil(mrb_state *mrb, mrb_value self)
{
  mrb_float fltself = mrb_float(self);
  struct Bignum *bigself = float_to_bignum(mrb, F(ceil)(fltself));
  return new_bignum(mrb, bigself, FIXNUM_CONVERT);
}

/* 15.2.9.3.10 Float#floor */
static mrb_value
float_floor(mrb_state *mrb, mrb_value self)
{
  mrb_float fltself = mrb_float(self);
  struct Bignum *bigself = float_to_bignum(mrb, F(floor)(fltself));
  return new_bignum(mrb, bigself, FIXNUM_CONVERT);
}

/* Convert a Float to Bignum or Fixnum */
static mrb_value
float_to_int(mrb_state *mrb, mrb_value self, mrb_bool fixnum_conv)
{
  mrb_float fltself = mrb_float(self);
  struct Bignum *bigself;

  if (isnan(fltself)) {
    mrb_raise(mrb, E_FLOATDOMAIN_ERROR, "NaN");
  }
  if (isinf(fltself)) {
    mrb_raise(mrb, E_FLOATDOMAIN_ERROR, fltself < 0 ? "-Infinity" : "Infinity");
  }

  F(modf)(fltself, &fltself);
  bigself = float_to_bignum(mrb, fltself);
  return new_bignum(mrb, bigself, fixnum_conv);
}

/* 15.2.9.3.15 Float#to_i */
/* 15.2.9.3.16 Float#truncate */
static mrb_value
float_to_i(mrb_state *mrb, mrb_value self)
{
  return float_to_int(mrb, self, FIXNUM_CONVERT);
}

/* ------------------------------------------------------------------------*/
/* String to Integer conversion */
/* ------------------------------------------------------------------------*/

static mrb_value
string_to_int(mrb_state *mrb, mrb_value self, mrb_bool fixnum_conv)
{
  mrb_int base = 10;
  struct Bignum *bigself;

  mrb_get_args(mrb, "|i", &base);

  if (base < 0 || 36 < base || base == 1) {
    mrb_raisef(mrb, E_ARGUMENT_ERROR, "invalid radix %S", mrb_fixnum_value(base));
  }

  bigself = bn_from_str(mrb, RSTRING_PTR(self), RSTRING_LEN(self), base);
  return new_bignum(mrb, bigself, fixnum_conv);
}

/* 15.2.10.5.38 String#to_i */
static mrb_value
string_to_i(mrb_state *mrb, mrb_value self)
{
  return string_to_int(mrb, self, FIXNUM_CONVERT);
}

/* ------------------------------------------------------------------------*/
/* "to_big" */
/* ------------------------------------------------------------------------*/

static mrb_value
fixnum_to_big(mrb_state *mrb, mrb_value self)
{
  struct Bignum *bigself = fixnum_to_bignum(mrb, mrb_fixnum(self));
  return new_bignum(mrb, bigself, FALSE);
}

static mrb_value
bignum_to_big(mrb_state *mrb, mrb_value self)
{
  return self;
}

static mrb_value
float_to_big(mrb_state *mrb, mrb_value self)
{
  return float_to_int(mrb, self, FALSE);
}

static mrb_value
string_to_big(mrb_state *mrb, mrb_value self)
{
  return string_to_int(mrb, self, FALSE);
}

/* ------------------------------------------------------------------------*/
/* Conversion to Fixnum if small enough */
/* ------------------------------------------------------------------------*/

static mrb_value
fixnum_to_fix(mrb_state *mrb, mrb_value self)
{
  return self;
}

static mrb_value
bignum_to_fix(mrb_state *mrb, mrb_value self)
{
  /* Can we return a Fixnum? */
  mrb_value fix = bignum_to_fixnum(DATA_PTR(self));
  return mrb_fixnum_p(fix) ? fix : self;
}

/* ------------------------------------------------------------------------*/
/* Coerce (15.2.7.4.4) */
/* ------------------------------------------------------------------------*/

static mrb_value
fixnum_coerce(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value pair;

  mrb_get_args(mrb, "o", &other);

  pair = mrb_ary_new_capa(mrb, 2);
  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum.coerce(Fixnum) */
    mrb_ary_set(mrb, pair, 0, other);
    mrb_ary_set(mrb, pair, 1, self);
    break;
  case num_bignum:
    /* Fixnum.coerce(Bignum) */
    {
      struct Bignum *bigself = fixnum_to_bignum(mrb, mrb_fixnum(self));
      mrb_ary_set(mrb, pair, 0, other);
      mrb_ary_set(mrb, pair, 1, new_bignum(mrb, bigself, FALSE));
    }
    break;
  case num_float:
    /* Fixnum.coerce(Float) */
    mrb_ary_set(mrb, pair, 0, other);
    mrb_ary_set(mrb, pair, 1, mrb_float_value(mrb, mrb_fixnum(self)));
    break;
  default:
    {
      mrb_value fltother;

      if (!mrb_respond_to(mrb, other, mrb_intern_lit(mrb, "to_f"))) {
        goto coerce_fail;
      }
      fltother = mrb_funcall(mrb, other, "to_f", 0);
      if (!mrb_float_p(fltother)) {
        goto coerce_fail;
      }
      mrb_ary_set(mrb, pair, 0, fltother);
      mrb_ary_set(mrb, pair, 1, mrb_float_value(mrb, mrb_fixnum(self)));
    }
    break;
  }

  return pair;

coerce_fail:
  mrb_raise(mrb, E_TYPE_ERROR, "cannot convert to float");
  return mrb_nil_value();
}

static mrb_value
bignum_coerce(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value pair;

  mrb_get_args(mrb, "o", &other);

  pair = mrb_ary_new_capa(mrb, 2);
  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum.coerce(Fixnum) */
    {
      struct Bignum *bigother = fixnum_to_bignum(mrb, mrb_fixnum(other));
      mrb_ary_set(mrb, pair, 0, new_bignum(mrb, bigother, FALSE));
      mrb_ary_set(mrb, pair, 1, self);
    }
    break;
  case num_bignum:
    /* Bignum.coerce(Bignum) */
    mrb_ary_set(mrb, pair, 0, other);
    mrb_ary_set(mrb, pair, 1, self);
    break;
  case num_float:
    /* Bignum.coerce(Float) */
    {
      mrb_float fltself = bn_to_float(DATA_PTR(self));
      mrb_ary_set(mrb, pair, 0, other);
      mrb_ary_set(mrb, pair, 1, mrb_float_value(mrb, fltself));
    }
    break;
  default:
    {
      mrb_float fltself = bn_to_float(DATA_PTR(self));
      mrb_value fltother;

      if (!mrb_respond_to(mrb, other, mrb_intern_lit(mrb, "to_f"))) {
        goto coerce_fail;
      }
      fltother = mrb_funcall(mrb, other, "to_f", 0);
      if (!mrb_float_p(fltother)) {
        goto coerce_fail;
      }
      mrb_ary_set(mrb, pair, 0, fltother);
      mrb_ary_set(mrb, pair, 1, mrb_float_value(mrb, fltself));
    }
    break;
  }

  return pair;

coerce_fail:
  mrb_raise(mrb, E_TYPE_ERROR, "cannot convert to float");
  return mrb_nil_value();
}

/* ------------------------------------------------------------------------*/
void
mrb_mruby_bignum_gem_init(mrb_state *mrb)
{
  struct RClass *integer = mrb_class_get(mrb, "Integer");
  struct RClass *fixnum  = mrb->fixnum_class;
  struct RClass *rfloat  = mrb->float_class;
  struct RClass *string  = mrb->string_class;

  struct RClass *bignum = mrb_define_class(mrb, "Bignum", integer);
  MRB_SET_INSTANCE_TT(bignum, MRB_TT_DATA);

  /* Redefined Fixnum methods */
  mrb_define_method(mrb, fixnum, "<=>",      fixnum_cmp,    MRB_ARGS_REQ(1)); /* 15.2.9.3.6  */
  mrb_define_method(mrb, fixnum, "==",       fixnum_eq,     MRB_ARGS_REQ(1)); /* 15.2.8.3.7  */
  mrb_define_method(mrb, fixnum, "+",        fixnum_plus,   MRB_ARGS_REQ(1)); /* 15.2.8.3.1  */
  mrb_define_method(mrb, fixnum, "-",        fixnum_minus,  MRB_ARGS_REQ(1)); /* 15.2.8.3.2  */
  mrb_define_method(mrb, fixnum, "*",        fixnum_mul,    MRB_ARGS_REQ(1)); /* 15.2.8.3.3  */
  mrb_define_method(mrb, fixnum, "/",        fixnum_div,    MRB_ARGS_REQ(1)); /* 15.2.8.3.4  */
  mrb_define_method(mrb, fixnum, "%",        fixnum_mod,    MRB_ARGS_REQ(1)); /* 15.2.8.3.5  */
  mrb_define_method(mrb, fixnum, "&",        fixnum_and,    MRB_ARGS_REQ(1)); /* 15.2.8.3.9  */
  mrb_define_method(mrb, fixnum, "|",        fixnum_or,     MRB_ARGS_REQ(1)); /* 15.2.8.3.10 */
  mrb_define_method(mrb, fixnum, "^",        fixnum_xor,    MRB_ARGS_REQ(1)); /* 15.2.8.3.11 */
  mrb_define_method(mrb, fixnum, "<<",       fixnum_lshift, MRB_ARGS_REQ(1)); /* 15.2.8.3.12 */
  mrb_define_method(mrb, fixnum, ">>",       fixnum_rshift, MRB_ARGS_REQ(1)); /* 15.2.8.3.13 */
  mrb_define_method(mrb, fixnum, "eql?",     fixnum_eql,    MRB_ARGS_REQ(1)); /* 15.2.8.3.16 */
  mrb_define_method(mrb, fixnum, "to_big",   fixnum_to_big, MRB_ARGS_NONE());
  mrb_define_method(mrb, fixnum, "to_fix",   fixnum_to_fix, MRB_ARGS_NONE());
  mrb_define_method(mrb, fixnum, "divmod",   fixnum_divmod, MRB_ARGS_REQ(1));
  mrb_define_method(mrb, fixnum, "quo",      fixnum_quo,    MRB_ARGS_REQ(1));
  mrb_define_method(mrb, fixnum, "**",       fixnum_pow,    MRB_ARGS_REQ(1));
  mrb_define_method(mrb, fixnum, "coerce",   fixnum_coerce, MRB_ARGS_REQ(1)); /* 15.2.7.4.4 */

  /* Bignum methods */
  mrb_define_method(mrb, bignum, "<=>",      bignum_cmp,    MRB_ARGS_REQ(1)); /* 15.2.9.3.6  */
  mrb_define_method(mrb, bignum, "==",       bignum_eq,     MRB_ARGS_REQ(1)); /* 15.2.8.3.7  */
  mrb_define_method(mrb, bignum, "+",        bignum_plus,   MRB_ARGS_REQ(1)); /* 15.2.8.3.1  */
  mrb_define_method(mrb, bignum, "-",        bignum_minus,  MRB_ARGS_REQ(1)); /* 15.2.8.3.2  */
  mrb_define_method(mrb, bignum, "*",        bignum_mul,    MRB_ARGS_REQ(1)); /* 15.2.8.3.3  */
  mrb_define_method(mrb, bignum, "/",        bignum_div,    MRB_ARGS_REQ(1)); /* 15.2.8.3.4  */
  mrb_define_method(mrb, bignum, "%",        bignum_mod,    MRB_ARGS_REQ(1)); /* 15.2.8.3.5  */
  mrb_define_method(mrb, bignum, "~",        bignum_rev,    MRB_ARGS_NONE()); /* 15.2.8.3.8  */
  mrb_define_method(mrb, bignum, "&",        bignum_and,    MRB_ARGS_REQ(1)); /* 15.2.8.3.9  */
  mrb_define_method(mrb, bignum, "|",        bignum_or,     MRB_ARGS_REQ(1)); /* 15.2.8.3.10 */
  mrb_define_method(mrb, bignum, "^",        bignum_xor,    MRB_ARGS_REQ(1)); /* 15.2.8.3.11 */
  mrb_define_method(mrb, bignum, "<<",       bignum_lshift, MRB_ARGS_REQ(1)); /* 15.2.8.3.12 */
  mrb_define_method(mrb, bignum, ">>",       bignum_rshift, MRB_ARGS_REQ(1)); /* 15.2.8.3.13 */
  mrb_define_method(mrb, bignum, "eql?",     bignum_eql,    MRB_ARGS_REQ(1)); /* 15.2.8.3.16 */
  mrb_define_method(mrb, bignum, "hash",     bignum_hash,   MRB_ARGS_NONE()); /* 15.2.8.3.18 */
  mrb_define_method(mrb, bignum, "to_f",     bignum_to_f,   MRB_ARGS_NONE()); /* 15.2.8.3.23 */
  mrb_define_method(mrb, bignum, "to_s",     bignum_to_s,   MRB_ARGS_OPT(1)); /* 15.2.8.3.25 */
  mrb_define_method(mrb, bignum, "inspect",  bignum_to_s,   MRB_ARGS_NONE());
  mrb_define_method(mrb, bignum, "to_big",   bignum_to_big, MRB_ARGS_NONE());
  mrb_define_method(mrb, bignum, "to_fix",   bignum_to_fix, MRB_ARGS_NONE());
  mrb_define_method(mrb, bignum, "divmod",   bignum_divmod, MRB_ARGS_REQ(1));
  mrb_define_method(mrb, bignum, "quo",      bignum_quo,    MRB_ARGS_REQ(1));
  mrb_define_method(mrb, bignum, "**",       bignum_pow,    MRB_ARGS_REQ(1));
  mrb_define_method(mrb, bignum, "coerce",   bignum_coerce, MRB_ARGS_REQ(1)); /* 15.2.7.4.4 */

  /* Redefined Float methods */
  mrb_define_method(mrb, rfloat, "<=>",      float_cmp,     MRB_ARGS_REQ(1)); /* 15.2.9.3.1  */
  mrb_define_method(mrb, rfloat, "==",       float_eq,      MRB_ARGS_REQ(1)); /* 15.2.9.3.2  */
  mrb_define_method(mrb, rfloat, "+",        float_plus,    MRB_ARGS_REQ(1)); /* 15.2.9.3.3  */
  mrb_define_method(mrb, rfloat, "-",        float_minus,   MRB_ARGS_REQ(1)); /* 15.2.9.3.4  */
  mrb_define_method(mrb, rfloat, "*",        float_mul,     MRB_ARGS_REQ(1)); /* 15.2.9.3.5  */
  mrb_define_method(mrb, rfloat, "/",        float_div,     MRB_ARGS_REQ(1)); /* 15.2.9.3.6  */
  mrb_define_method(mrb, rfloat, "%",        float_mod,     MRB_ARGS_REQ(1)); /* 15.2.9.3.7  */
  mrb_define_method(mrb, rfloat, "ceil",     float_ceil,    MRB_ARGS_NONE()); /* 15.2.9.3.8  */
  mrb_define_method(mrb, rfloat, "floor",    float_floor,   MRB_ARGS_NONE()); /* 15.2.9.3.10 */
  mrb_define_method(mrb, rfloat, "to_i",     float_to_i,    MRB_ARGS_NONE()); /* 15.2.9.3.15 */
  mrb_define_method(mrb, rfloat, "to_int",   float_to_i,    MRB_ARGS_NONE());
  mrb_define_method(mrb, rfloat, "to_big",   float_to_big,  MRB_ARGS_NONE());
  mrb_define_method(mrb, rfloat, "truncate", float_to_i,    MRB_ARGS_NONE()); /* 15.2.9.3.16 */
  mrb_define_method(mrb, rfloat, "divmod",   float_divmod,  MRB_ARGS_REQ(1));
  mrb_define_method(mrb, rfloat, "quo",      float_quo,     MRB_ARGS_REQ(1));
  mrb_define_method(mrb, rfloat, "**",       float_pow,     MRB_ARGS_REQ(1));

  /* Redefined String methods */
  mrb_define_method(mrb, string, "to_i",     string_to_i,   MRB_ARGS_OPT(1)); /* 15.2.9.3.15 */
  mrb_define_method(mrb, string, "to_int",   string_to_i,   MRB_ARGS_OPT(1));
  mrb_define_method(mrb, string, "to_big",   string_to_big, MRB_ARGS_OPT(1));

  /* ZeroDivisionError */
  mrb_define_class(mrb, "ZeroDivisionError", mrb->eStandardError_class);
}

void
mrb_mruby_bignum_gem_final(mrb_state *mrb)
{
}
