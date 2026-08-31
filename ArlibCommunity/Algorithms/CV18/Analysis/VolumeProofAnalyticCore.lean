/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofPrimitives
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSchedule
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCost
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofProductAccuracy
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofInitialCoupling
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofIdealProduct
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofSharpMoments
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation

open MeasureTheory

namespace ArlibCommunity.Algorithms.CV18

/-!
# Analytic core of the CV18 base run

All operational, measure-theoretic, warm-start, terminal-moment, and structural
query-count obligations have been discharged before this point. The public
theorem in this module makes the remaining quantitative content explicit as
hypotheses: the log-concave truncation tail, sharp phase-amortized ratio
moments, ball-walk mixing, and dependent product accuracy.
-/

/-- A strong, reusable sufficient condition for the post-initial sampling
step: domination of the entire dependent output law by the independent output
law plus an error measure of mass at most `1/16`. -/
def FigureOnePostInitialLawCoupling
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) : Prop :=
  MeasureLeUpTo
    ((truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
      (figureOneContinuationLaw explicitVolumeCoolingSchedule q I oracle))
    (figureOneIdealEstimateLaw q I)
    (ENNReal.ofReal (1 / 16 : ℝ))

/-- The exact remaining sampling statement used by the accuracy theorem.  It
allows the paper's covariance/truncation analysis and does not unnecessarily
require simultaneous coupling of every sample in a long cooling schedule. -/
def FigureOnePostInitialMixingBound
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) : Prop :=
  ((truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
    (figureOneContinuationLaw explicitVolumeCoolingSchedule q I oracle))
      (accurateOutcome q I)ᶜ ≤
    (figureOneIdealExperimentLaw q I)
      {samples | initialGaussianIntegral q * figureOneIdealProduct q samples ∉
        accurateOutcome q I} + ENNReal.ofReal (1 / 16 : ℝ)

theorem figureOnePostInitialMixingBound_of_lawCoupling
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I)
    (hmixing : FigureOnePostInitialLawCoupling q I oracle) :
    FigureOnePostInitialMixingBound q I oracle := by
  have h := MeasureLeUpTo.event_le hmixing (accurateOutcome q I)ᶜ
  rw [figureOneIdealEstimateLaw_apply q I
    (accurateOutcome_measurable q I).compl] at h
  exact h

theorem figureOne_base_accuracy_of_analytic_inputs
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I)
    (hsharp : FigureOneSharpAcceleratedMoments q I)
    (htrunc : FigureOneRadialTruncationBound q I)
    (hmixing : FigureOnePostInitialMixingBound q I oracle) :
    3 / 4 ≤
      outcomeProbability
        (volumeAlgorithmLaw
          (fun q => baseVolumeCooling figureOnePrimitives
            explicitVolumeCoolingSchedule q) q I oracle)
        (accurateOutcome q I) := by
  let μ : Measure ℝ :=
    volumeAlgorithmLaw
      (fun q => baseVolumeCooling figureOnePrimitives
        explicitVolumeCoolingSchedule q) q I oracle
  have hstrong := figureOneBaseVolumeCooling_stronglyMeasurable
    explicitVolumeCoolingSchedule q I oracle
  let _ : IsProbabilityMeasure μ := by
    unfold μ volumeAlgorithmLaw
    exact MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
      hstrong.estimateMeasurable
  apply outcomeProbability_ge_three_quarters_of_failure_le μ q I
  change
    (baseVolumeCooling figureOnePrimitives explicitVolumeCoolingSchedule q).runEstimate
        oracle.query (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ)
  calc
    _ ≤ ((truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
        (figureOneContinuationLaw explicitVolumeCoolingSchedule q I oracle))
          (accurateOutcome q I)ᶜ + ENNReal.ofReal (q.eps / 64) :=
      figureOneBaseVolumeCooling_event_le_idealStart_add
        explicitVolumeCoolingSchedule q I oracle (accurateOutcome q I)ᶜ
          (accurateOutcome_measurable q I).compl
    _ ≤ ((figureOneIdealExperimentLaw q I)
          {samples | initialGaussianIntegral q * figureOneIdealProduct q samples ∉
          accurateOutcome q I} + ENNReal.ofReal (1 / 16 : ℝ)) +
          ENNReal.ofReal (q.eps / 64) := by
      gcongr
      exact hmixing
    _ ≤ (ENNReal.ofReal (1 / 8 : ℝ) + ENNReal.ofReal (1 / 16 : ℝ)) +
          ENNReal.ofReal (q.eps / 64) := by
      gcongr
      exact figureOneIdealScaledProduct_realVolume_failure_le_one_div_8
        q I hsharp htrunc
    _ ≤ (ENNReal.ofReal (1 / 8 : ℝ) + ENNReal.ofReal (1 / 16 : ℝ)) +
          ENNReal.ofReal (1 / 64 : ℝ) := by
      gcongr
      exact q.heps.2.le
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 8)
          (by norm_num : (0 : ℝ) ≤ 1 / 16),
        ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 8 + 1 / 16)
          (by norm_num : (0 : ℝ) ≤ 1 / 64)]
      apply ENNReal.ofReal_le_ofReal
      norm_num

/-- The accelerated localization/moment input is now discharged
unconditionally; only radial truncation and post-initial walk mixing remain. -/
theorem figureOne_base_accuracy_of_truncation_and_mixing
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I)
    (htrunc : FigureOneRadialTruncationBound q I)
    (hmixing : FigureOnePostInitialMixingBound q I oracle) :
    3 / 4 ≤
      outcomeProbability
        (volumeAlgorithmLaw
          (fun q => baseVolumeCooling figureOnePrimitives
            explicitVolumeCoolingSchedule q) q I oracle)
        (accurateOutcome q I) :=
  figureOne_base_accuracy_of_analytic_inputs q I oracle
    (figureOneSharpAcceleratedMoments q I) htrunc hmixing

/-!
The unconditional CV18 capstone is intentionally not asserted here. Closing it
requires proofs of `FigureOneRadialTruncationBound` and
`FigureOnePostInitialMixingBound` from the paper's radial-tail and lazy
ball-walk arguments. The accelerated localization input is discharged in
`VolumeProofSharpMoments`.
-/

end ArlibCommunity.Algorithms.CV18
