/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceDependentAssembly
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledHistoryAppend

/-! # Scheduled trace capstone with executable semantics discharged -/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- The exact finite-schedule interpreter theorem removes `hpoint` from the
loss-preserving trace capstone.  The remaining premises are precisely the
finite Lemma 7.15/7.17 moment and dependence estimates. -/
theorem figureOneFinalScheduledBalancedBase_failure_le_of_trace_moments
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hWint : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      Integrable (scheduledBalancedTracePhaseVariable q j)
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hmeanPos : ∀ j, 0 < scheduledFigureOneTraceTruncatedMean q I j)
    (hrawMeanPos : ∀ j, 0 < scheduledFigureOneTraceRawMean q I j)
    (hrawMean_le : ∀ j,
      scheduledFigureOneTraceRawMean q I j ≤
        2 * scheduledFigureOneTraceTruncatedMean q I j)
    (hmeanSecond : ∀ j,
      scheduledFigureOneTraceTruncatedMean q I j ^ 2 ≤
        scheduledFigureOneTraceTruncatedSecond q I j)
    (hrawSecond : ∀ j,
      scheduledFigureOneTraceRawMean q I j ^ 2 ≤
        2 * scheduledFigureOneTraceTruncatedSecond q I j)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) i)
        (scheduledFigureOneTraceTruncatedPhase q I (i + 1))
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hrelative : ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I) i ≤
        2 * dependentPhaseMeanProduct
          (scheduledFigureOneTraceTruncatedMean q I) i ^ 2)
    (htailSecond :
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedSecond q I)
            (figureOneDependentPhaseCount q) ≤
        (1 + q.eps ^ 2 / 16) *
          dependentPhaseMeanProduct
            (scheduledFigureOneTraceTruncatedMean q I)
            (figureOneDependentPhaseCount q) ^ 2)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (scheduledFigureOneTraceTruncatedMean q I)
        (figureOneDependentPhaseCount q))) :
    (figureOneFinalScheduledBalancedBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  exact figureOneFinalScheduledBalancedBase_failure_le_of_trace_lemma717bc
    q I oracle hrounded
      (scheduledBalancedFigureOnePointContinuation_runEstimate_eq_forwardHistory_map
        figureOneFinalScheduledBalancedParameters q I oracle)
      hWint hmeanPos hrawMeanPos hrawMean_le hmeanSecond hrawSecond hind
      hrelative htailSecond hmeanApprox

#print axioms figureOneFinalScheduledBalancedBase_failure_le_of_trace_moments

end ArlibCommunity.Algorithms.CV18
