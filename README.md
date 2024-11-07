## Formalization of PEGs using the Coq proof assistant

This repository formalizes the syntax and the semantics of [PEGs]
using the [Coq] proof assistant.
It also formalizes the algorithm implemented in [LPeg]
for detecting well-formed PEGs,
and proves that it terminates and is correct.
Correctness here implies in termination of the parsing procedure.

## Syntax

We define use the desugared syntax of PEGs
first established by (Ford, 2024).
It contains the empty pattern, terminals,
non-terminals, repetitions, not-predicates,
sequences, and choices.
From these, we can construct more complex patterns
such as character classes from choices,
and and-predicates from not-predicates.
This simplification helps us formalize PEGs
without losing expressiveness.

## Semantics

We define the match procedure both
as a fixed point function which takes
a gas counter and returns an optional result,
and an inductive predicate.
The fixed point definition is interesting
for proving termination,
and the inductive predicate is useful
for proving correctness,
and other complex results
which may benefit from proofs by induction.

## Well-formedness

We define the algorithm implemented in [LPeg]
that detects well-formed PEGs,
a subset of complete PEGs whose
detection is decidable.
Ford proved that, in the general case,
the problem of identifying complete PEGs
is undecidable, so this is a conservative
approach that ensures termination.

## Files

The main files are:

- `Pattern.v`: patterns (a.k.a. expressions)
- `Grammar.v`: PEG syntax
- `Match.v`: PEG semantics
- `Coherent.v`: valid nonterminals
- `Verifyrule.v`: left-recursive rules
- `Nullable.v`: nullable patterns
- `Checkloops.v`: degenerate loops
- `Verifygrammar.v`: well-formedness

Auxiliar files are:

- `Tactics.v`: auxiliary proof tactics
- `Pigeonhole.v`: states and proves the pigeonhole principle
- `Strong.v`: states and proves the strong induction primitive
- `Suffix.v`: defines the suffix and proper suffix relations, and proves some results about them

## Building the project

In order to build the project, please run the following command on the root of the project.

```sh
make -f CoqMakefile
```

[PEGs]: https://doi.org/10.1145/964001.964011
[Coq]: https://coq.inria.fr/
[LPeg]: https://www.inf.puc-rio.br/~roberto/lpeg/
