mruby-bignum
============

A self-contained Bignum implementation for mruby.  Implements the methods found in ISO Ruby for the Integer class, and a
few others found in CRuby.

Full integration with mruby requires certain changes to the core.  Most such changes have been submitted to the main mruby
project, but they have not been added to the master branch at this writing (6 September 2014).  Until that changes, it is
necessary for best results to use a patched mruby.  This version can be had from https://github.com/chasonr/mruby/archive/bignum-support.zip , or by cloning https://github.com/chasonr/mruby.git and checking out the bignum-support branch.
