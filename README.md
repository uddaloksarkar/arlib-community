# arlib-community

`arlib-community` is an importable Lean 4 library for algorithms and their
analysis. It is the algorithm-facing companion to Arlib: Arlib supplies reusable
data structures and mathematical foundations, while this library organizes
algorithm implementations, reductions, correctness results, lower bounds, and
explicit complexity models by theory.

The public Lean module is `ArlibCommunity`.

## Using the library

From another local Lean project, add this dependency to `lakefile.toml`:

```toml
[[require]]
name = "arlibCommunity"
path = "../arlib-community"
```

Then update Lake and import the complete library:

```bash
lake update arlibCommunity
```

```lean
import ArlibCommunity
```

This root imports every mutually compatible theory. Continuous MCMC is
temporarily a separate import because the current upstream finite and continuous
Markov-chain staging trees both define `Arlib.MarkovChains.flow_apply`. Use:

```lean
import ArlibCommunity.Theories.ContinuousMCMC
```

Do not combine that module with `ArlibCommunity.Theories.FiniteMarkovChains`
until the upstream namespace collision is migrated.

For a smaller dependency, import one theory directly:

```lean
import ArlibCommunity.Theories.ContinuousMCMC
import ArlibCommunity.Theories.KnowledgeCompilation
```

The current development checkout resolves core Arlib from the sibling
`../arlib-pr3` directory. A published version should replace that path in
`lakefile.toml` with a pinned Git revision of Arlib.

## How to read this repository

Read the repository in this order:

1. Use `ArlibCommunity/Theories/<Name>.lean` to see a theory's public imports.
   These are the stable entry points intended for downstream formalizations.
2. Read the corresponding files below `Theories/<name>/src/` when auditing the
   migrated proofs or their original authorship. These are verbatim snapshots,
   not the public module path.
3. Consult [`REFERENCES.md`](REFERENCES.md) for citations and source provenance,
   and [`CONTRIBUTING.md`](CONTRIBUTING.md) for the core/community ownership rule.

## Directory layout

```text
ArlibCommunity.lean                 public root; imports compatible theories
ArlibCommunity/
  Init.lean                        shared initialization
  Theories/*.lean                  narrow public imports, including optional MCMC
Examples/Import.lean               downstream-style import smoke test
Theories/
  <theory>/src/                    verbatim migration snapshot
CONTRIBUTING.md                    ownership rule and contribution workflow
REFERENCES.md                      citations and source provenance
```

## Complexity convention

Every complexity statement must name the primitive it counts. Depending on the
theory this may be an oracle query, comparison, sample, transition, Bellman
backup, circuit node, communicated bit, or retained row. A unit-cost oracle
model is not automatically a unit-cost machine model, and a Markov-chain mixing
bound is not automatically a running-time bound. Each theory README records the
relevant distinction.

## Building

Use Lean `v4.33.0`, then run from this directory:

```bash
lake build
```

The files under `Theories/*/src` preserve the migration inputs and are not Lake
targets. The compiled API is the `ArlibCommunity` module tree. `lake build`
verifies the compatible root; the command below verifies the optional
continuous-MCMC entry point separately:

```bash
lake build ArlibCommunity.Theories.ContinuousMCMC
```
