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

#print axioms
  MeasureLeUpTo.measure_relativeDeviation_le_of_reference_moments
#print axioms
  initializedScheduledRetainedHistory_relativeDeviation_le_of_resetReference

end ArlibCommunity.Algorithms.CV18
