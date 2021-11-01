# Short demonstrations of Coq

## Equations

  **File**: equations_sort.v

  A small file illustrating how to use the Equations extension to define
  a simple sorting function and prove its correctness.

  This demonstration was last tested with coq.8.13.2 and
   coq-equations.1.3~beta2+8.13

  The file `Equations_complements.v` should be compiled first.

## Interval

  **File**: sin_properties.v

  A small file illustrating mathematical proofs about functions, including
  graphical display of their curves.

  This demonstration was last tested with coq.1.13.2 and coq-interval.4.3.0

## compiler

  First clone [the semantics repository](https://github.com/ybertot/semantics.html)

  **File**: little.v

  **File**: asm.v

  A toy language given with a collection of language theory tools:
  opeerational semantics given as *natural semantics* (big step
  operational semantics), proofs of equivalence with small-step
  operational semantics, and a functional description of an
  interpreter.  File `asm.v` contains a description of a small stack machine,
  its assembly language (8 instructions), a compiler, and its proof of
  correctness.

## VST

  A live demo of the results in Appel&Bertot2020 about C code implementing
  a square root function.

  This demonstration was last tested with coq.1.13.2 and coq-vst.2.8
  (compcert.3.9)