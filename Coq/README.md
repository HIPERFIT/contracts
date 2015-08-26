# Certified Symbolic Management of Financial Multi-Party Contracts [![Build Status](https://travis-ci.org/HIPERFIT/contracts.svg?branch=master)](https://travis-ci.org/HIPERFIT/contracts)

This directory contains the certified implementation of the financial
multi-party contract language described in the paper
["Certified Symbolic Management of Financial Multi-Party Contracts"](../doc/icfp2015.pdf). It
also includes the Haskell implementation that has been extracted from
the Coq implementation along with examples that illustrate the use of
the extracted Haskell library.

## File Structure

- [Syntax.v](Syntax.v) defines the language's syntax.
- [Typing.v](Typing.v) defines the type system.
- [Denotational.v](Denotational.v) defines the denotational semantics;
  [DenotationalTyped.v](DenotationalTyped.v) proves that the
  denotational semantics is total on well-typed contracts.
- [Equivalence.v](Equivalence.v) proves some contract equivalences.
- [Antisymmetry.v](Antisymmetry.v) proves antisymmetry of the
  denotational semantics.
- [SyntacticCausality.v](SyntacticCausality.v) and
  [ContextualCausality.v](ContextualCausality.v) implement syntactic
  causality checks and prove them sound.
- [TimedTyping.v](TimedTyping.v) gives the time-indexed type system
  and proves that well-typed contracts are causal. In addition, it
  defines type inference procedure and proves it sound and complete.
- [Reduction.v](Reduction.v) defines the reduction semantics and
  proves it adequate for the denotational semantics.
- [Specialise.v](Specialise.v) defines specialisation of contracts
  (partial evaluation w.r.t. a partial external environment) and
  proves it correct.
- [Horizon.v](Horizon.v) defines the (syntactic) horizon of a contract
  and proves that it is semantically correct.

## Theorems from the Paper


The list below details where the theorems (and lemmas, corollaries
etc.) from the paper
["Certified Symbolic Management of Financial Multi-Party Contracts"](http://www.diku.dk/~paba/pubs/files/bahr15icfp-preprint.pdf)
can be found in the Coq formalisation:

- Lemma 1: lemma `translateExp_ext` in [TranslateExp.v](TranslateExp.v)
- Lemma 2: theorem `sem_antisym` in [Antisymmetry.v](Antisymmetry.v)
- Proposition 3: theorem `Esem_typed_total` and `Csem_typed_total` in
  [DenotationalTyped.v](DenotationalTyped.v)
- Proposition 4: theorem `horizon_sound` in [Horizon.v](Horizon.v)
- Proposition 5: lemma `TiTyE_type` and theorem `TiTyC_type` in [TimedTyping.v](TimedTyping.v)
- Theorem 6: corollary `TiTyC_causal` in [TimedTyping.v](TimedTyping.v)
- Lemma 7: lemma `TiTyE_open` and `TiTyC_open` in [TimedTyping.v](TimedTyping.v)
- Theorem 8: theorem `inferC_sound` and inferC_complete in [TimedTyping.v](TimedTyping.v)
- Corollary 9: corollary `has_type_causal` in [TimedTyping.v](TimedTyping.v)
- Theorem 10: theorem `specialiseExp_sound` and `specialise_sound` in [Specialise.v](Specialise.v)
- Theorem 11: (i) theorem `red_sound1` and `red_sound2`, (ii) theorem
  `red_preservation`, and (iii) theorem `red_progress` in [Reduction.v](Reduction.v)


## Other Definitions and Properties from the Paper

The function `adv` from the paper is defined as `redfun` in
[Reduction.v](Reduction.v). The soundness and completeness of `redfun`
is proved by Theorem `redfun_red` respectively Theorem `red_redfun` in
[Reduction.v](Reduction.v).

The functions `spE` and `spC` from the paper are defined in
[Specialise.v](Specialise.v) as `specialiseExp` and
`specialise`, respectively.

## Code Extraction & Examples


The [Extraction](Extraction) subdirectory implements a simple
extraction of the Coq definitions to Haskell code using Coq's built-in
extraction facility. For convenience, the extracted Haskell code is
included in this repository. To reproduce the code extraction from Coq
to Haskell use the Makefile in [Extraction](Extraction):

```shell
make
cd Extraction
make
```

The extracted Haskell code provides a library for writing and managing
contracts embedded in Haskell. The
[Extraction/Examples](Extraction/Examples) subdirectory contains a
number of example contracts that are written using the extracted
Haskell library.


## Logical Axioms


The Coq formalisation uses logical axioms for three abstract data
types:

- We assume the types `Asset` and `Party` with decidable equality
  (cf. [Syntax.v](Syntax.v)).
- We assume the type `FMap` of finite mappings given by a standard set
  of operations on finite mappings together with a set of axioms that
  specify their properties (cf. [FinMap.v](FinMap.v)).
  
## Technical Details

### Dependencies

- To check the proofs: Coq 8.4pl5
- To step through the proofs: GNU Emacs 24.3.1, Proof General 4.2
- To use extracted Haskell library: GHC 7.8.4

### Proof Checking

To check and compile the complete Coq development, you can use the
`Makefile`:

```shell
> make
```
