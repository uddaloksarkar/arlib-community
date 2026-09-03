/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledResetAverageSecond
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofDependentProduct

/-!
# Event-level transfer from a fixed-reset reference

An additive measure comparison does not control an unbounded second moment:
the residual mass may carry arbitrarily large values.  It does, however,
transfer every failure event with exactly its stated mass.  We therefore run
the target-centered Markov argument on the exact-coordinate reference and
only then transfer the resulting deviation event to the executable history.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

open _root_.Arlib

/-- Target-centered Markov on a reference probability law, followed by an
honest one-sided event transfer to the executable law. -/
theorem MeasureLeUpTo.measure_relativeDeviation_le_of_reference_moments
    {Omega : Type*} [MeasurableSpace Omega]
    {actual reference : Measure Omega} [IsProbabilityMeasure reference]
    {error : ENNReal} (hcomparison : MeasureLeUpTo actual reference error)
    {X : Omega → ℝ} (hX : MemLp X 2 reference)
    {target eps eta delta : ℝ} (htarget : 0 < target) (heps : 0 < eps)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta)
    (hmeanLower : (1 - eta) * target ≤ ∫ omega, X omega ∂reference)
    (hsecond : (∫ omega, X omega ^ 2 ∂reference) ≤
      (1 + delta) * target ^ 2) :
    actual {omega | eps * target ≤ |X omega - target|} ≤
      ENNReal.ofReal ((delta + 2 * eta) / eps ^ 2) + error := by
  have href := measure_relativeDeviation_le_of_target_moments
    reference hX htarget heps heta hdelta hmeanLower hsecond
  calc
    actual {omega | eps * target ≤ |X omega - target|} ≤
        reference {omega | eps * target ≤ |X omega - target|} + error :=
      hcomparison.event_le _
    _ ≤ ENNReal.ofReal ((delta + 2 * eta) / eps ^ 2) + error := by
      gcongr

/-- Scheduled specialization of the event-level transfer.  The hypotheses
are precisely the reference-average facts supplied by the exact-coordinate
`L³` equation-(6) construction; no executable raw second moment is assumed.
-/
theorem initializedScheduledRetainedHistory_relativeDeviation_le_of_resetReference
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (reference : Measure (RetainedSampleHistory (AmbientSpace q.n)))
    [IsProbabilityMeasure reference]
    (hcomparison : MeasureLeUpTo
      (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
      reference (scheduledResetReferenceError q (count - 1)))
    {target eps eta delta : ℝ} (htarget : 0 < target) (heps : 0 < eps)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta)
    (hmem : MemLp (fun history =>
      sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) count history /
        (count : ℝ)) 2 reference)
    (hmeanLower : (1 - eta) * target ≤
      ∫ history, sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) count history /
          (count : ℝ) ∂reference)
    (hsecond :
      (∫ history, (sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) count history /
          (count : ℝ)) ^ 2 ∂reference) ≤
        (1 + delta) * target ^ 2) :
    (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        {history | eps * target ≤
          |sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) count history /
              (count : ℝ) - target|} ≤
      ENNReal.ofReal ((delta + 2 * eta) / eps ^ 2) +
        scheduledResetReferenceError q (count - 1) := by
  exact hcomparison.measure_relativeDeviation_le_of_reference_moments
    hmem htarget heps heta hdelta hmeanLower hsecond

/-- Complete within-Gaussian-phase event adapter.  Exact coordinate moments
and the equation-(6) arithmetic are proved on one fixed-reset reference, and
only the resulting deviation event is transferred to the executable history.
-/
theorem initializedScheduledRetainedHistory_relativeDeviation_le_of_coordinate_moments
    (q : VolumeParams) (I : VolumeInput q.n) (phase count : ℕ)
    (hcount : 0 < count)
    (hcountMax : count ≤ figureOneDependentMaxSampleCount q)
    {A factor delta eps : ℝ} (hA : 0 < A) (hdelta : 0 ≤ delta)
    (heps : 0 < eps)
    (hcoordinateSecond :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 2
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤
        factor *
          (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)) x
            ∂(truncatedGaussianProbability q I (scheduleValue q phase)
              (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ^ 2)
    (hcoordinateThird :
      (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x ^ 3
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ≤ A ^ 3)
    (hmomentBudget :
      (1 + (factor - 1) / (count : ℝ)) *
          (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)) x
            ∂(truncatedGaussianProbability q I (scheduleValue q phase)
              (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ^ 2 +
        3 * (figureOneDependentEpsilon q +
            3 * (scheduledResetReferenceError q (count - 1)).toReal) ^
              (1 / 3 : ℝ) *
          (1 - 1 / (count : ℝ)) * A ^ 2 ≤
        (1 + delta) *
          (∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
              (scheduleValue q (phase + 1)) x
            ∂(truncatedGaussianProbability q I (scheduleValue q phase)
              (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))) ^ 2) :
    let target :=
      ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
          (scheduleValue q (phase + 1)) x
        ∂(truncatedGaussianProbability q I (scheduleValue q phase)
          (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
    (initializedScheduledRetainedHistoryLaw q I phase (count - 1))
        {history | eps * target ≤
          |sequentialPrefixSum
            (retainedSampleObservation
              (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
                (scheduleValue q (phase + 1)))) count history /
              (count : ℝ) - target|} ≤
      ENNReal.ofReal (delta / eps ^ 2) +
        scheduledResetReferenceError q (count - 1) := by
  dsimp only
  let mean :=
    ∫ x, gaussianRatioWeight (n := q.n) (scheduleValue q phase)
        (scheduleValue q (phase + 1)) x
      ∂(truncatedGaussianProbability q I (scheduleValue q phase)
        (scheduleValue_pos q phase) : Measure (AmbientSpace q.n))
  have hmean : 0 < mean := by
    rw [show mean =
        gaussianIntegral (truncatedBody q I) (scheduleValue q (phase + 1)) /
          gaussianIntegral (truncatedBody q I) (scheduleValue q phase) by
      simpa [mean] using
        gaussianRatioWeight_mean_eq q I (scheduleValue_pos q phase)]
    exact div_pos
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q (phase + 1)))
      (gaussianIntegral_pos q (truncatedVolumeInput q I)
        (scheduleValue_pos q phase))
  obtain ⟨reference, hprob, hcomparison, hmem, hrefMean, hrefSecond⟩ :=
    exists_scheduledRetainedResetReference_average_secondMoment
      q I phase count hcount hcountMax hA hmean.le (by
        exact le_rfl) (by simpa [mean] using hcoordinateSecond)
        hcoordinateThird
  let _ : IsProbabilityMeasure reference := hprob
  have hrefMean' :
      (∫ history, sequentialPrefixSum
        (retainedSampleObservation
          (gaussianRatioWeight (n := q.n) (scheduleValue q phase)
            (scheduleValue q (phase + 1)))) count history /
          (count : ℝ) ∂reference) = mean := by
    simpa [mean] using hrefMean
  have hresult :=
    initializedScheduledRetainedHistory_relativeDeviation_le_of_resetReference
      q I phase count reference hcomparison (target := mean) (eps := eps)
      (eta := 0) (delta := delta) hmean heps (by norm_num) hdelta hmem
      (by simpa [hrefMean'])
      (hrefSecond.trans (by simpa [mean] using hmomentBudget))
  simpa [mean] using hresult

#print axioms
  MeasureLeUpTo.measure_relativeDeviation_le_of_reference_moments
#print axioms
  initializedScheduledRetainedHistory_relativeDeviation_le_of_resetReference
#print axioms
  initializedScheduledRetainedHistory_relativeDeviation_le_of_coordinate_moments

end ArlibCommunity.Algorithms.CV18
