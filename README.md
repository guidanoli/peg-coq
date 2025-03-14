## Formalization of PEGs using the Coq proof assistant

This repository formalizes the syntax and the semantics of [PEGs]
using the [Coq] proof assistant.
It also formalizes the algorithm implemented in [LPeg]
for detecting well-formed PEGs,
and proves that it terminates and is correct.
Correctness here implies in termination of the parsing procedure.
It also formalizes the definition of "first" implemented in [LPeg],
used to optimize certain types of patterns such as choices.
We also prove the choice optimization is correct.

## Syntax

We define use the desugared syntax of PEGs
first established by Ford.
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

## First

We loosely define here "first" as a conservative set of
characters that a string can start in order to match a pattern.
To be more precise, if a string starts with a character
that is not in the first set of a pattern,
then the match is guaranteed to fail.
To take into consideration the match against empty strings,
the function that computes the first set also outputs a Boolean value
which indicates whether the pattern may match the empty string or not.
If it returns false, then the pattern fails to match the empty string.
Otherwise, it may or may not match the empty string.
Besides the input grammar and pattern,
the function also takes a character set called "follow" as parameter.
The purpose of this parameter is to properly define first for sequence patterns.
In the sequence `p1; p2`, we use the first of `p2` as the follow of `p1`.

This definition is used by LPeg to optimize patterns such as choices.
Given a choice pattern `p1 / p2`, if `p1` does not match the empty string,
and the first sets of `p1` and `p2` are disjoint,
then LPeg converts the choice pattern into `&[cs1] p1 / ![cs1] p2`,
where `cs1` is the first set of `p1`.
In terms of instructions of the LPeg virtual machine,
this is equivalent to a test instruction,
which makes matching against this pattern more performant.
We prove that this optimization is correct in Coq.

## Files

The main files are:

- `Syntax.v`: PEG syntax
- `Match.v`: PEG semantics
- `Coherent.v`: valid nonterminals
- `Verifyrule.v`: left-recursive rules
- `Nullable.v`: nullable patterns
- `Checkloops.v`: degenerate loops
- `Verifygrammar.v`: well-formedness
- `First.v`: definition of first (used for optimization)

Auxiliar files are:

- `Tactics.v`: auxiliary proof tactics
- `Pigeonhole.v`: states and proves the pigeonhole principle
- `Strong.v`: states and proves the strong induction primitive
- `Suffix.v`: defines the suffix and proper suffix relations, and proves some results about them
- `Charset.v`: defines character sets and operations on them, and proves some lemmas about them
- `Startswith.v`: defines the "starts with" function, and proves some lemmas about it
- `Equivalent.v`: defines equivalent patterns, proves some lemmas about them, and examples

## Building the project

In order to build the project, you first need to make sure you have the following dependencies installed on your system.

- Coq 8.18.0 or later
- GNU Make

Then, you can build the project by running `make` on the root of the project.

[PEGs]: https://doi.org/10.1145/964001.964011
[Coq]: https://coq.inria.fr/
[LPeg]: https://www.inf.puc-rio.br/~roberto/lpeg/
