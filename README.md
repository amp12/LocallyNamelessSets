# Locally Nameless Sets
Agda code accompanying the paper: Andrew Pitts, _Locally Nameless Sets_

- [paper](https://github.com/amp12/LocallyNamelessSets/blob/main/html/locns-pop.pdf)
- [browsable source code](https://github.com/amp12/LocallyNamelessSets/blob/main/html/Everything.html)
- [zip archive](https://github.com/amp12/LocallyNamelessSets/blob/main/html/agda-locns.zip) of the source code

Agda (version 2.6.2.2) was used to develop the theory of locally nameless sets and to check some of the proofs in the paper. The code mainly targets proofs that involve equational reasoning combined with the use of atoms and indices that are sufficiently fresh (via cofinite quantification). Some of these proofs involve a lot of nested case analysis on elements of sets with decidable equality (atoms and indices); some of the equational axioms are unfamiliar-looking and combinatorially complicated; and it is easy to forget to check necessary freshness conditions are satisfied when doing informal proofs. For all these reasons the use of an interactive theorem prover to produce machine-checked proofs was essential to gain assurance that the results in the paper are correct.

The Agda code is stand-alone: some standard definitions (that might otherwise be called from Agda's Standard Library) are collected in the file Prelude.agda. The last part of the development requires function extensionality, which we postulate (file FunExt.agda).
