ELBA
========

Exact Loop Bound Analysis using the <a href="https://github.com/Z3Prover/z3">Z3</a> SMT solver. It iteratively synthesizes an exact loop bound for single loop programs. Find more details in the <a href="https://danielmriley.github.io/papers/elba.pdf">PLDI'25</a> paper.

Installation
============

Compiles with gcc-7 (on Linux) and clang-1001 (on Mac). Assumes preinstalled <a href="https://gmplib.org/">GMP</a>, and Boost (libboost-system1.79-dev) packages. Additionally, armadillo package to get candidates from behaviors. 

* `cd aeval ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3)
* `make` (again) to build elba

The binary of elba can be found at `build/tools/elba/`.
Run `elba --help` for the usage info.

The tools print `Success ...` if a bound is found.

Benchmarks
==========

Collection of the SMT-LIB2 translations of single loop programs can be found at `bench_elba`.

