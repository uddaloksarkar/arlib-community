/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledPhaseL2
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedHistoryMomentBridge
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofActualMeanTruncation

/-!
# Actual-mean moment assembly for the executable scheduled trace

The older phase-moment assembly is centered at the exact ideal phase means.
The scheduled finite execution is only approximately stationary, so its
truncation is instead centered at its actual mean.  This file records the
same sharp one-phase truncation estimates with that actual center and then
assembles the finite products used by CV18 Lemmas 7.14--7.15.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- The ideal factor attached to the actual chronological phase is at most
two. -/
theorem figureOneChronologicalMomentFactor_le_two
    (q : VolumeParams) (j : ℕ) :
    figureOneChronologicalMomentFactor q j ≤ 2 :=
  figureOneIdealPhaseFactor_le_two q (figureOneChronologicalPhaseAt q j)

/-- Truncating at the actual mean can only decrease the second moment. -/
theorem scheduledFigureOneTrace_truncatedSecond_le_rawSecond
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hrawPos : 0 < scheduledFigureOneTraceRawMean q I j)
    (hWmem : MemLp (scheduledBalancedTracePhaseVariable q j) 2
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q))) :
    scheduledFigureOneTraceTruncatedSecond q I j ≤
      ∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q) := by
  let mu := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let raw := scheduledFigureOneTraceRawMean q I j
  let alpha := figureOneDependentAlpha q
  let W := scheduledBalancedTracePhaseVariable q j
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  have halpha : 0 < alpha := figureOneDependentAlpha_pos q
  have hV0 : ∀ trace, 0 ≤ min (W trace) (alpha * raw) := by
    intro trace
    exact le_min (scheduledBalancedTracePhaseVariable_nonnegative q j trace)
      (mul_nonneg halpha.le hrawPos.le)
  have hVmem : MemLp (fun trace => min (W trace) (alpha * raw)) 2 mu := by
    apply MemLp.of_bound
      ((measurable_scheduledBalancedTracePhaseVariable q j).min
        measurable_const).aestronglyMeasurable
      (alpha * raw)
    filter_upwards with trace
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 trace)]
    exact min_le_right _ _
  change (∫ trace, min (W trace) (alpha * raw) ^ 2 ∂mu) ≤
    ∫ trace, W trace ^ 2 ∂mu
  apply integral_mono hVmem.integrable_sq hWmem.integrable_sq
  intro trace
  exact (sq_le_sq₀ (hV0 trace)
    (scheduledBalancedTracePhaseVariable_nonnegative q j trace)).2
      (min_le_left _ _)

/-- With the paper's sharp chronological second-moment factor, truncation at
`alpha * actualMean` loses at most the standard multiplicative
`1 + 1 / alpha`. -/
theorem scheduledFigureOneTrace_rawMean_le_one_add_inv_alpha_mul_truncatedMean
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ)
    (hrawPos : 0 < scheduledFigureOneTraceRawMean q I j)
    (hWmem : MemLp (scheduledBalancedTracePhaseVariable q j) 2
      (scheduledBalancedForwardTraceLaw
        figureOneFinalScheduledBalancedParameters q I
        (figureOneDependentPhaseCount q)))
    (hsecond :
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        figureOneChronologicalMomentFactor q j *
          scheduledFigureOneTraceRawMean q I j ^ 2) :
    scheduledFigureOneTraceRawMean q I j ≤
      (1 + 1 / figureOneDependentAlpha q) *
        scheduledFigureOneTraceTruncatedMean q I j := by
  let mu := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I
      (figureOneDependentPhaseCount q)
  let raw := scheduledFigureOneTraceRawMean q I j
  let alpha := figureOneDependentAlpha q
  let W := scheduledBalancedTracePhaseVariable q j
  let _ : IsProbabilityMeasure mu :=
    scheduledBalancedForwardTraceLaw_isProbabilityMeasure
      figureOneFinalScheduledBalancedParameters q I _
  have halpha : (1024 : ℝ) ≤ alpha := figureOneDependentAlpha_ge_1024 q
  have hcap : 0 < alpha * raw := mul_pos (by linarith) hrawPos
  have htrunc := integral_min_ge_integral_sub_secondMoment_div_four mu
    (hWmem.integrable (by norm_num)) hWmem.integrable_sq
    (scheduledBalancedTracePhaseVariable_nonnegative q j) hcap
  have hfactor : figureOneChronologicalMomentFactor q j ≤ 2 :=
    figureOneChronologicalMomentFactor_le_two q j
  have hsecondTwo : (∫ trace, W trace ^ 2 ∂mu) ≤ 2 * raw ^ 2 :=
    hsecond.trans (mul_le_mul_of_nonneg_right hfactor (sq_nonneg raw))
  have hloss : (∫ trace, W trace ^ 2 ∂mu) / (4 * (alpha * raw)) ≤
      raw / (2 * alpha) := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hcap)]
    field_simp [show alpha ≠ 0 by linarith]
    nlinarith [hsecondTwo]
  have hmeanLower : (1 - 1 / (2 * alpha)) * raw ≤
      scheduledFigureOneTraceTruncatedMean q I j := by
    change (∫ trace, min (W trace) (alpha * raw) ∂mu) ≥
      raw - (∫ trace, W trace ^ 2 ∂mu) / (4 * (alpha * raw)) at htrunc
    change (1 - 1 / (2 * alpha)) * raw ≤
      ∫ trace, min (W trace) (alpha * raw) ∂mu
    calc
      (1 - 1 / (2 * alpha)) * raw = raw - raw / (2 * alpha) := by ring
      _ ≤ raw - (∫ trace, W trace ^ 2 ∂mu) / (4 * (alpha * raw)) :=
        sub_le_sub_left hloss raw
      _ ≤ _ := htrunc
  have hinv0 : 0 ≤ 1 / alpha := by positivity
  have hinv1 : 1 / alpha ≤ 1 :=
    (div_le_one (by linarith : 0 < alpha)).2 (by linarith)
  have hcoefficient : 1 ≤
      (1 + 1 / alpha) * (1 - 1 / (2 * alpha)) := by
    rw [show (1 + 1 / alpha) * (1 - 1 / (2 * alpha)) =
      1 + (1 / alpha) * (1 - 1 / alpha) / 2 by ring]
    nlinarith [mul_nonneg hinv0 (sub_nonneg.mpr hinv1)]
  have hscale := mul_le_mul_of_nonneg_left hmeanLower
    (by positivity : 0 ≤ 1 + 1 / alpha)
  change raw ≤ (1 + 1 / alpha) *
    scheduledFigureOneTraceTruncatedMean q I j
  calc
    raw = 1 * raw := by ring
    _ ≤ ((1 + 1 / alpha) * (1 - 1 / (2 * alpha))) * raw :=
      mul_le_mul_of_nonneg_right hcoefficient hrawPos.le
    _ = (1 + 1 / alpha) * ((1 - 1 / (2 * alpha)) * raw) := by ring
    _ ≤ _ := hscale

#print axioms figureOneChronologicalMomentFactor_le_two
#print axioms scheduledFigureOneTrace_truncatedSecond_le_rawSecond
#print axioms scheduledFigureOneTrace_rawMean_le_one_add_inv_alpha_mul_truncatedMean

end ArlibCommunity.Algorithms.CV18
