/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.AuditCheck
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLazyProperProgram
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofLazyProperFailure
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedyToTarget
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPhaseMixing
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStrongStepMixing
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyPhaseMixing
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedyWarmStart
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofInitialSpeedyWarmStart
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSubprobabilityMixing
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSpeedySpectral
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyKLS
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyRejectionSemantics
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyAcceptance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportanceMoments
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportanceProgram
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportanceLaw
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCappedDominance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportanceConcentration
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFreshPhaseStart
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofStrongInitialWarmStart
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofGlobalQueryCap
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRejection
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryProgram
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryApproximation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScaleInvariant
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMarkovEmpirical
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMarkovVariance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCollectSemantics
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProperCollect
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyProperProgram
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKLSCore
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.Convexity.SpeedyGaussianMixing

/-!
# CV18 accelerated Gaussian cooling

The currently verified, problem-specific analysis of Cousins and Vempala's
accelerated Gaussian-cooling volume algorithm [CV18]. The implementation and
all discharged analytic infrastructure are exposed here. Radial truncation,
sharp moments, proper-step cost at the advertised Figure-1 step,
the executable lazy proper-step clock, speedy-Gaussian mixing, and amplification
are unconditional. The full assembly
`volumeTheorem_of_postInitialMixing` has exactly one remaining premise: the
dependent post-initial walk bound for the executable kernel.

See `Analysis/README.md` for a module-level status and source audit.
-/
