# Contributing to arlib-community

## Build, test, audit

```bash
lake exe cache get                    # prebuilt Mathlib oleans — always first
lake build                            # the library
lake test                             # the worked examples in ArlibCommunityTest/
lake env lean scripts/AxiomAudit.lean # no sorry, no extra axioms
```

CI runs exactly those four. `lake env lean ArlibCommunity/Path/To/File.lean`
type-checks a single file without taking Lake's workspace lock, which is the
fast way to iterate; a change that crosses modules still needs a real
`lake build`.

## What belongs here, and what belongs in arlib

The two repositories split by *what a result is about*, not by who needed it.

| It is about | It goes in |
| --- | --- |
| A subject — probability, concentration, Markov chains, information theory, knowledge compilation, communication complexity, generic `Finset`/`List` helpers | [arlib](https://github.com/meelgroup/arlib) |
| A named algorithm — the law of its counter, the arithmetic of its schedule, its termination argument | here |

Two rules on top of that.

**Only the problem-independent half.** An algorithm's analysis divides into a
generic half and a half that exhibits the structure the algorithm needs for one
particular counting or sampling problem. Only the generic half belongs in a
shared library; the rest stays in the project that uses it. An entry that cannot
be stated without naming a problem is a sign the split has not been found yet.

**A lemma with no algorithm in it belongs upstream.** If while analysing an
algorithm you prove something general — a `Finset` identity, a tail bound, a
fact about Poisson masses — send it to arlib and import it. Material drifting
into the wrong repository is the failure mode this split exists to prevent.

## Adding an algorithm

Create `ArlibCommunity/Algorithms/<Name>/` together with
`ArlibCommunity/Algorithms/<Name>.lean`, which re-exports every module in the
directory, and add `import ArlibCommunity.Algorithms.<Name>` to
`ArlibCommunity/Algorithms.lean`.

The sub-area root is not a stub: it carries a docstring saying what the
algorithm is, what half of its analysis is here, what is deliberately left to
the caller, and a module-by-module table. Each algorithm takes its own namespace
`ArlibCommunity.Algorithms.<Name>`, because entries are independent of one
another and their short names would collide.

Add a worked example to `ArlibCommunityTest/`, and the paper to
[REFERENCES.md](REFERENCES.md) with the key its docstrings cite.

## House style

arlib's
[CONVENTIONS.md](https://github.com/meelgroup/arlib/blob/main/CONVENTIONS.md)
governs here too: naming, namespacing, statement shape, a docstring on every
declaration, explicit numeric bounds rather than `O`/`Ω` asymptotics. The build
must be warning-free.

The hard invariant, enforced by CI: no `sorry`, and no axiom beyond the three
Mathlib itself uses — `propext`, `Classical.choice`, `Quot.sound`.
