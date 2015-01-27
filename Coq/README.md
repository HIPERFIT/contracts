Coq Formalisation of Contract Language
======================================

This is a formalisation of the contract language. The module structure
is as follows:

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
  and proves that "well-timed" (i.e. well-typed in this type system)
  contracts are causal. In addition, it defines type inference
  procedure and proves it sound.
- [Reduction.v](Reduction.v) defines the (total) reduction semantics
  and proves it sound and complete.
- [PartialReduction.v](PartialReduction.v) defines the partial
  reduction semantics and proves it sound.
- [Specialise.v](Specialise.v) defines specialisation of contracts
  (partial evaluation w.r.t. a partial external environment) and
  proves it correct.
- [Horizon.v](Horizon.v) defines the (syntactic) horizon of a contract
  and proves that it is semantically correct.


Extraction
==========

The [Extraction](Extraction) subdirectory implements a simple
extraction of the Coq definitions to Haskell code using Coq's built-in
extraction facility. To extract the Coq definitions to Haskell use the
Makefile in [Extraction](Extraction):

```shell
make
cd Extraction
make
```

Logical Axioms
==============

The Coq formalisation uses logical axioms for three abstract data
types:

- We assume the types `Asset` and `Party` with decidable equality
  (cf. [Syntax.v](Syntax.v)).
- We assume the type `FMap` of finite mappings given by a standard set
  of operations on finite mappings together with a set of axioms that
  specify their properties (cf. [FinMap.v](FinMap.v)).

