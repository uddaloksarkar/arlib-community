/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.AuditCheck
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAverageConductance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKernelBridge
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.SpeedyGaussianMixing

/-!
# CV18 accelerated Gaussian cooling

The currently verified, problem-specific analysis of Cousins and Vempala's
accelerated Gaussian-cooling volume algorithm [CV18]. The implementation and
all discharged analytic infrastructure are exposed here. Radial truncation,
sharp moments, proper-step cost at the small step, speedy-Gaussian mixing, and
amplification are unconditional. The full assembly
`volumeTheorem_of_postInitialMixing` has exactly one remaining premise: the
dependent post-initial walk bound for the executable kernel.

See `Analysis/README.md` for a module-level status and source audit.
-/
