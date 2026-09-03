/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceFullGoodBad
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceCapstoneExecutable

/-! # The scheduled trace capstone with CV18 Lemma 7.17(c) discharged -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- The raw-moment accuracy capstone no longer asks the caller to supply
CV18 Lemma 7.17(c); the executable loss-preserving trace proves it for every
phase internally. -/
theorem figureOneFinalScheduledBalancedBase_failure_le_of_trace_raw_moments_lemma717c
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hWmem : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      MemLp (scheduledBalancedTracePhaseVariable q j) 2
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)))
    (hrawMeanPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hrawSecondFour : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      (∫ trace, scheduledBalancedTracePhaseVariable q j trace ^ 2
        ∂scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)) ≤
        4 * scheduledFigureOneTraceRawMean q I j ^ 2)
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
  exact figureOneFinalScheduledBalancedBase_failure_le_of_trace_raw_moments
    q I oracle hrounded hWmem hrawMeanPos hrawSecondFour
      (figureOneScheduledTrace_lemma717c q I) hrelative htailSecond hmeanApprox

#print axioms figureOneFinalScheduledBalancedBase_failure_le_of_trace_raw_moments_lemma717c

end ArlibCommunity.Algorithms.CV18
