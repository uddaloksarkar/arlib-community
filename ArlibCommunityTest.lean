/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# ArlibCommunityTest — executable documentation

Short worked examples of arlib-community's public API, one module per area. They
exist for two reasons, in this order:

1. **They document.** Each example is the shortest honest answer to "how do I
   actually use this?", and unlike a README snippet it cannot rot: if the API
   changes underneath it, `lake test` goes red.
2. **They guard the API surface.** The library proper is internally consistent by
   construction. These examples are the only code that consumes the library the
   way a *downstream user* does, from outside, through `import ArlibCommunity`
   and the public namespaces — and they are also the only place that exercises
   the seam with arlib, the dependency.

They are deliberately not exhaustive and are not a proof-checking test suite —
the library's correctness is its own theorem statements, checked by the compiler,
plus the axiom audit in `scripts/AxiomAudit.lean`. Run them with `lake test`.
-/

import ArlibCommunityTest.Algorithms
