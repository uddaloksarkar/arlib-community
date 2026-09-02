/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceDependentAssembly
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledHistoryAppend

/-! # Scheduled trace capstone with executable semantics discharged -/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

private noncomputable def scheduledTracePhaseRepresentative
    (q : VolumeParams) (j : ℕ) : ℕ :=
  (j - 1) % figureOneDependentPhaseCount q + 1

private theorem scheduledTracePhaseRepresentative_pos
    (q : VolumeParams) (j : ℕ) :
    1 ≤ scheduledTracePhaseRepresentative q j := by
  simp [scheduledTracePhaseRepresentative]

private theorem scheduledTracePhaseRepresentative_le
    (q : VolumeParams) (j : ℕ) :
    scheduledTracePhaseRepresentative q j ≤ figureOneDependentPhaseCount q := by
  unfold scheduledTracePhaseRepresentative
  have hmod := Nat.mod_lt (j - 1) (figureOneDependentPhaseCount_pos q)
  omega

private theorem figureOneChronologicalPhaseAt_representative
    (q : VolumeParams) (j : ℕ) :
    figureOneChronologicalPhaseAt q j =
      figureOneChronologicalPhaseAt q
        (scheduledTracePhaseRepresentative q j) := by
  unfold figureOneChronologicalPhaseAt scheduledTracePhaseRepresentative
  congr 1
  apply Fin.ext
  simp only [Nat.add_sub_cancel]
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (figureOneDependentPhaseCount_pos q))]

private theorem scheduledBalancedTracePhaseVariable_representative
    (q : VolumeParams) (j : ℕ) :
    scheduledBalancedTracePhaseVariable q j =
      scheduledBalancedTracePhaseVariable q
        (scheduledTracePhaseRepresentative q j) := by
  funext trace
  unfold scheduledBalancedTracePhaseVariable
    scheduledBalancedTraceChronologicalPhaseVariable
    balancedCoolingChronologicalPhaseVariable
  rw [figureOneChronologicalPhaseAt_representative q j]

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
    (hmeanPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceTruncatedMean q I j)
    (hrawMeanPos : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      0 < scheduledFigureOneTraceRawMean q I j)
    (hrawMean_le : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      scheduledFigureOneTraceRawMean q I j ≤
        2 * scheduledFigureOneTraceTruncatedMean q I j)
    (hmeanSecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      scheduledFigureOneTraceTruncatedMean q I j ^ 2 ≤
        scheduledFigureOneTraceTruncatedSecond q I j)
    (hrawSecond : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
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
  have hrawRepresentative : ∀ j,
      scheduledFigureOneTraceRawMean q I j =
        scheduledFigureOneTraceRawMean q I
          (scheduledTracePhaseRepresentative q j) := by
    intro j
    unfold scheduledFigureOneTraceRawMean
    rw [scheduledBalancedTracePhaseVariable_representative q j]
  have hphaseRepresentative : ∀ j,
      scheduledFigureOneTraceTruncatedPhase q I j =
        scheduledFigureOneTraceTruncatedPhase q I
          (scheduledTracePhaseRepresentative q j) := by
    intro j
    funext trace
    unfold scheduledFigureOneTraceTruncatedPhase dependentTruncatedPhase
    rw [hrawRepresentative j,
      scheduledBalancedTracePhaseVariable_representative q j]
  have hmeanRepresentative : ∀ j,
      scheduledFigureOneTraceTruncatedMean q I j =
        scheduledFigureOneTraceTruncatedMean q I
          (scheduledTracePhaseRepresentative q j) := by
    intro j
    unfold scheduledFigureOneTraceTruncatedMean
    rw [hphaseRepresentative j]
  have hsecondRepresentative : ∀ j,
      scheduledFigureOneTraceTruncatedSecond q I j =
        scheduledFigureOneTraceTruncatedSecond q I
          (scheduledTracePhaseRepresentative q j) := by
    intro j
    unfold scheduledFigureOneTraceTruncatedSecond
    rw [hphaseRepresentative j]
  apply figureOneFinalScheduledBalancedBase_failure_le_of_trace_lemma717bc
    q I oracle hrounded
      (scheduledBalancedFigureOnePointContinuation_runEstimate_eq_forwardHistory_map
        figureOneFinalScheduledBalancedParameters q I oracle)
      hWint
  · intro j
    rw [hmeanRepresentative j]
    exact hmeanPos _ (scheduledTracePhaseRepresentative_pos q j)
      (scheduledTracePhaseRepresentative_le q j)
  · intro j
    rw [hrawRepresentative j]
    exact hrawMeanPos _ (scheduledTracePhaseRepresentative_pos q j)
      (scheduledTracePhaseRepresentative_le q j)
  · intro j
    rw [hrawRepresentative j, hmeanRepresentative j]
    exact hrawMean_le _ (scheduledTracePhaseRepresentative_pos q j)
      (scheduledTracePhaseRepresentative_le q j)
  · intro j
    rw [hmeanRepresentative j, hsecondRepresentative j]
    exact hmeanSecond _ (scheduledTracePhaseRepresentative_pos q j)
      (scheduledTracePhaseRepresentative_le q j)
  · intro j
    rw [hrawRepresentative j, hsecondRepresentative j]
    exact hrawSecond _ (scheduledTracePhaseRepresentative_pos q j)
      (scheduledTracePhaseRepresentative_le q j)
  · exact hind
  · exact hrelative
  · exact htailSecond
  · exact hmeanApprox

#print axioms figureOneFinalScheduledBalancedBase_failure_le_of_trace_moments

end ArlibCommunity.Algorithms.CV18
