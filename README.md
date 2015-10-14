# README #

This is an implementation of the following paper in Coq 8.5.

L. Birkedal, K. Støvring, and J. Thamsborg. The category-theoretic solution of recursive metric-space equations. Theoretical Computer Science, 411(47):4102–4122, Oct 2010. URL http://dx.doi.org/10.1016/j.tcs.2010.07.010.

It is built on top of the category theory development:
https://github.com/amintimany/Categories

## Coq version and compilation ##

* This development has been tested on Debian with Coq8.5-beta2
* It requires https://github.com/amintimany/Categories to be accessible by Coq.
The best way to get that is to install it using ``` make install ``` after compilation.
* To compile simply type
    * ``` ./configure ``` to produce the Makefile [1] and then
    * ``` make ``` to compile

[1] you will need to have coq_makefile to be on the path