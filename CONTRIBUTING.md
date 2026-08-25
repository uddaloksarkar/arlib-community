# Contributing to arlib-community

## Build, test, audit

```bash
lake exe cache get
lake build
lake test
lake env lean scripts/AxiomAudit.lean
```

CI runs those four checks. To iterate on one module without taking Lake's
workspace lock, use `lake env lean ArlibCommunity/Path/To/File.lean`. Changes
that cross module boundaries still need a full `lake build`.

## What belongs here, and what belongs in arlib

The two repositories split by what a result is about, not by who needed it.

| It is about | It goes in |
| --- | --- |
| Reusable foundations: probability, concentration, Markov chains, information theory, knowledge compilation, communication complexity, or generic helpers | [arlib](https://github.com/uddaloksarkar/arlib) |
| An algorithm, model, reduction, lower bound, or explicit resource analysis built on those foundations | here |

Only the problem-independent part of an analysis belongs in a shared library.
Problem-specific structure stays in the project that uses it. General lemmas
discovered while formalizing an application should move upstream to arlib.

## Adding an area

Put public modules below `ArlibCommunity/<Area>/` and provide an
`ArlibCommunity/<Area>.lean` import root. Add compatible roots to
`ArlibCommunity.lean`; keep intentionally incompatible or optional roots as
separate documented imports.

Add a downstream-style import example below `Examples/`, document the public
entry point in `README.md`, and record source references in `REFERENCES.md`.

## House style

Follow arlib's
[CONVENTIONS.md](https://github.com/uddaloksarkar/arlib/blob/arlib-core/CONVENTIONS.md)
for naming, namespaces, theorem statements, and docstrings. Complexity claims
must name the primitive resource they count rather than leaving the cost model
implicit.

The build must be warning-free. No declaration may depend on `sorryAx` or on an
axiom beyond `propext`, `Classical.choice`, and `Quot.sound`.
