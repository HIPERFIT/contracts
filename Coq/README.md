Coq Formalisation of Contract Language
======================================

This is a formalisation of the contract language. The module structure
is as follows:

- [Syntax.v](Syntax.v) defines the language's syntax.
- [Denotational.v](Denotational.v) defines the denotational semantics.
- [Equivalence.v](Equivalence.v) proves some contract equivalences.
- [Monotonicity.v](Monotonicity.v) proves monotonicity of the
  denotational semantics.
- [SyntacticCausality.v](SyntacticCausality.v) and
  [ContextualCausality.v](ContextualCausality.v) implement syntactic
  causality checks and prove them sound.
- [Reduction.v](Reduction.v) defines the reduction semantics and
  proves it sound and complete.
- [Horizon.v](Horizon.v) defines the (syntactic) horizon of a contract
  and proves that it is semantically correct.


Extraction
==========

The [Extraction](Extraction) subdirectory implements a simple
extraction of the Coq definitions to Haskell code using Coq's built-in
extraction facility. To extract the Coq definitions to Haskell use the
Makefile in [Extraction](Extraction):

```shell
cd Extraction
make
```
