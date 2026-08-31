/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.AuditCheck

/-!
# CV18 accelerated Gaussian cooling

The currently verified, problem-specific analysis of Cousins and Vempala's
accelerated Gaussian-cooling volume algorithm [CV18]. The implementation and
all discharged analytic infrastructure are exposed here. The unconditional
`O*(n^3)` volume theorem is not yet exported: radial truncation and dependent
ball-walk mixing remain explicit hypotheses of
`figureOne_base_accuracy_of_truncation_and_mixing`. The sharp accelerated
moment bound is unconditional.

See `Analysis/README.md` for a module-level status and source audit.
-/
