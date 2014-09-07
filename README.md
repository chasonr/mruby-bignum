mruby-bignum
============

A self-contained Bignum implementation for mruby.  Implements the methods found in ISO Ruby for the Integer class, and a
few others found in CRuby.

Full integration with mruby requires certain changes to the core.  Most such changes have been submitted to the main mruby
project, but they have not been added to the master branch at this writing (6 September 2014).  Until that changes, it is
necessary for best results to use a patched mruby.  This version can be had from https://github.com/chasonr/mruby/archive/bignum-support.zip , or by cloning https://github.com/chasonr/mruby.git and checking out the bignum-support branch.

A GMP-based Bignum gem is also available at https://github.com/chasonr/mruby-bignum/ .  GMP-based Bignums are much faster than this gem, but they require the [GMP library](https://gmplib.org/).

## Using mruby-bignum with the bignum-support branch

It is sufficient to clone the gem under the mrbgems directory of the mruby tree, and add `conf.gem :core => "mruby-bignum"` to the defaults.gembox file.  Mruby will then support Bignums in conformance to the ISO standard.

The include/mrbconf.h file contains the line `#define MRB_BIGNUM_INTEGRATION`.  The purpose of this symbol is to signal the Bignum gem that it is linked to a Bignum-capable mruby.  This symbol enables the Bignum gem to produce Bignum literals when passed an Integer literal that is too large for a Fixnum.  If this symbol is disabled, such literals go back to being Floats.

The mruby-bignum gem also responds to `MRB_BIGNUM_INTEGRATION`.  If enabled, all calculations that return integers will convert them to Fixnum if they are small enough; otherwise, any operation involving Bignums and returning an integer will always return a Bignum.  The operators `**`, `<<` and `>>` consider only the left operands for this purpose.  The `to_big` and `to_fix` methods are not affected by `MRB_BIGNUM_INTEGRATION`, as described below.

## Using mruby-bignum with the mainline mruby

As with the bignum-support branch, clone the gem under the mrbgems directory of the mruby tree, and add `conf.gem :core => "mruby-bignum"` to the defaults.gembox file.

The mruby-bignum gem is significantly limited when used this way:

* A nasty bug (mruby/mruby issue #2557) affects `Bignum#+` and `Bignum#-` when the right side is a Fixnum literal with value from -127 to -1.  The minus sign is never passed to the method.  To get around this, use the `to_fix` method on the right side:  `x + -7.to_fix`.  The `Fixnum#to_fix` method returns its receiver, but using it here prevents a broken optimization from being done.

* The mainline mruby does not support overriding the +, -, * and / operators in the Float and Fixnum classes.  To get around this, use the `to_big` method on the left hand side:  `x = 1000000.to_big * 1000000` sets `x` to a Bignum with the value of 1,000,000,000,000.

* Large integer literals (those too large to form a Fixnum) are converted to Float.  To make a Bignum literal, write a string and use `to_i` (or `to_big`):  `"12345678901234567890".to_i`.  Note that `12345678901234567890.to_i`, without the quotes, produces a Float and then converts it to Bignum; this may lose the least significant bits.

The mruby-bignum gem attempts to mitigate these issues by implementing a rule of "once a Bignum, always a Bignum unless explicitly converted".  That is, if either input to most binary operators is a Bignum, the output is always a Bignum unless you use the `to_fix` method.  The operators `**`, `<<` and `>>` consider only the left operands.

## The `to_big` and `to_fix` methods

The `to_big` and `to_fix` methods are provided to ease the use of mruby-bignum with the mainline mruby; but they are also available with the bignum-support branch.  They work the same with either version of mruby:

* `to_big` converts its receiver (a Fixnum, Bignum, Float or String) to an integer by the same rules as `to_i`, but always returns a Bignum.
* `to_fix` converts its receiver (a Fixnum, Bignum, Float or String) to an integer by the same rules as `to_i`, but always attempts to convert to Fixnum, even with the mainline mruby.  It returns a Bignum if the integer is too large for a Fixnum.

Other integer conversion methods (`to_i`, `to_int`, `ceil` and `floor`) return a Fixnum if possible when used with bignum-support, and always a Bignum when used with mainline mruby.

## Available methods

The following methods are provided, or modified from the original mruby:

* `Numeric#coerce(rhs)` implements `coerce` according to the ISO standard.
* `Fixnum#coerce` and `Bignum#coerce` override `Numeric#coerce` so that a combination of Fixnum and Bignum returns two Bignums instead of two Floats.
* `<=>`, `==` and `eql?` are extended so that Bignums can be compared.
* `+`, `-`, `*`, `%`, `divmod`, `<<`, `>>` and `**` are extended so that Bignums can occur as operands.  If a result exceeds the range of Fixnum, a Bignum is produced.
* `&`, `|` and `^` are extended to work with Bignums.
* `/` replaces the nonconformant behavior of mruby's `/` with an ISO-conformant one -- return an integer, rounded down -- and works with Bignum operands and produces Bignum results.
* `quo` is not part of the ISO standard, but is documented in CRuby as producing the most exact quotient, which for integer inputs is a Rational.  The mruby-bignum gem does not implement Rational, and so `quo` produces a Float.  It is extended to work with Bignums.
* `to_big` and `to_fix` are modified forms of `to_i`, described above, to mitigate issues arising when using mruby-bignum with the mainline mruby.
* `hash` is defined, so that Bignums can act as hash keys.
* `to_f`, `to_s` and `inspect` are provided for Bignum receivers.
* `ceil` and `floor` are redefined for Floats so they return a Bignum, as the ISO standard provides.
* `to_i` and `to_int` are redefined for Float and String receivers to produce a Bignum if the result is too large for a Fixnum.
