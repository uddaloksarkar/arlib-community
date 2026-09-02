/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofChronologicalKernelInstantiation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCorrectedErrorAllocation

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

noncomputable section

/-- Uniform envelope for one complete Figure-One phase. -/
noncomputable def figureOnePhaseReplacementBudget (q : VolumeParams) : ENNReal :=
  figureOneDependentMaxSampleCount q •
    ENNReal.ofReal (figureOnePerSampleMixingError q)

/-- The corrected per-sample theorem, enlarged only from the actual phase
sample count to the uniform Figure-One maximum. -/
theorem MeasureLeUpTo.map_iteratedKernelLaw_of_figureOne_phase_max
    {State Output : Type*} [MeasurableSpace State] [MeasurableSpace Output]
    (q : VolumeParams)
    (actualK idealK : ℕ → State → Measure State)
    (initial : Measure State)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    {totalBudget : ENNReal}
    (hstep : ∀ i, MeasureLeUpTo
      ((iteratedKernelLaw idealK initial i).bind (actualK i))
      (iteratedKernelLaw idealK initial (i + 1)) totalBudget)
    (hbudget : totalBudget ≤
      ENNReal.ofReal (figureOnePerSampleMixingError q))
    (k : ℕ) (hk : k ≤ figureOneDependentMaxSampleCount q)
    (average : State → Output) (haverage : Measurable average) :
    MeasureLeUpTo
      ((iteratedKernelLaw actualK initial k).map average)
      ((iteratedKernelLaw idealK initial k).map average)
      (figureOnePhaseReplacementBudget q) := by
  have h := MeasureLeUpTo.map_iteratedKernelLaw_of_figureOne_phase_budget
    q actualK idealK initial hactualMeas hactualProb hstep hbudget
      k average haverage
  exact h.mono_error <| nsmul_le_nsmul_left (show
    0 ≤ ENNReal.ofReal (figureOnePerSampleMixingError q) from bot_le) hk

/-- Summing the uniform complete-phase envelope over the finite cooling
horizon occupies exactly the `1/64` final event-transfer slot. -/
theorem figureOnePhaseReplacementBudget_sum_le (q : VolumeParams) :
    figureOneDependentPhaseCount q • figureOnePhaseReplacementBudget q ≤
      ENNReal.ofReal (1 / 64 : ℝ) := by
  unfold figureOnePhaseReplacementBudget
  calc
    figureOneDependentPhaseCount q •
        (figureOneDependentMaxSampleCount q •
          ENNReal.ofReal (figureOnePerSampleMixingError q)) =
      (figureOneDependentMaxSampleCount q *
        figureOneDependentPhaseCount q) •
          ENNReal.ofReal (figureOnePerSampleMixingError q) := by
        simp [nsmul_eq_mul, Nat.cast_mul]
        ring
    _ ≤ ENNReal.ofReal (1 / 64 : ℝ) :=
      figureOne_exactChance_event_budget_le q

/-- Outer chronological replacement: a complete-phase domination at every
step yields the mapped scalar-law `1/64` premise consumed by the balanced
base-run theorem. -/
theorem MeasureLeUpTo.map_figureOnePhaseIteration
    {State Output : Type*} [MeasurableSpace State] [MeasurableSpace Output]
    (q : VolumeParams)
    (actualPhase idealPhase : ℕ → State → Measure State)
    (initial : Measure State)
    (hactualMeas : ∀ i, Measurable (actualPhase i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualPhase i state))
    (hphase : ∀ i, MeasureLeUpTo
      ((iteratedKernelLaw idealPhase initial i).bind (actualPhase i))
      (iteratedKernelLaw idealPhase initial (i + 1))
      (figureOnePhaseReplacementBudget q))
    (output : State → Output) (houtput : Measurable output) :
    MeasureLeUpTo
      ((iteratedKernelLaw actualPhase initial
        (figureOneDependentPhaseCount q)).map output)
      ((iteratedKernelLaw idealPhase initial
        (figureOneDependentPhaseCount q)).map output)
      (ENNReal.ofReal (1 / 64 : ℝ)) := by
  have h := MeasureLeUpTo.map_iteratedKernelLaw_exactChance
    actualPhase idealPhase initial hactualMeas hactualProb hphase
      (figureOneDependentPhaseCount q) output houtput
  exact h.mono_error (figureOnePhaseReplacementBudget_sum_le q)

/-- Final schedule adapter.  A concrete chronological phase construction
only has to identify its two terminal mapped laws and prove the per-phase
replacement premise; the complete analytic and base-run assembly is then
automatic. -/
theorem balancedFigureOneBase_failure_le_of_phaseIteration
    {State : Type*} [MeasurableSpace State]
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hrounded : WellRounded q I)
    (actualPhase idealPhase : ℕ → State → Measure State)
    (initial : Measure State)
    (hactualMeas : ∀ i, Measurable (actualPhase i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualPhase i state))
    (hphase : ∀ i, MeasureLeUpTo
      ((iteratedKernelLaw idealPhase initial i).bind (actualPhase i))
      (iteratedKernelLaw idealPhase initial (i + 1))
      (figureOnePhaseReplacementBudget q))
    (output : State → ℝ) (houtput : Measurable output)
    (hactualLaw :
      (iteratedKernelLaw actualPhase initial
          (figureOneDependentPhaseCount q)).map output =
        (balancedFigureOnePostInitialHistoryLaw parameters q I).map
          (fun history => initialGaussianIntegral q *
            dependentPhaseSampleProduct
              (balancedCoolingChronologicalPhaseVariable q)
              (figureOneDependentPhaseCount q) history))
    (hidealLaw :
      (iteratedKernelLaw idealPhase initial
          (figureOneDependentPhaseCount q)).map output =
        (figureOneIdealExperimentLaw q I).map
          (fun samples => initialGaussianIntegral q *
            dependentPhaseSampleProduct
              (figureOneChronologicalIdealCoordinate q)
              (figureOneDependentPhaseCount q) samples)) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
        explicitVolumeCoolingSchedule q).runEstimate oracle.query
          (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  have htransfer := MeasureLeUpTo.map_figureOnePhaseIteration q
    actualPhase idealPhase initial hactualMeas hactualProb hphase output houtput
  rw [hactualLaw, hidealLaw] at htransfer
  exact balancedFigureOneBase_failure_le_of_mappedLaw
    parameters q I oracle hrounded htransfer

/-! ## Paper-faithful Lemma 7.15 specialization

The exact-chance route above is useful when a full-history replacement is
available.  The following theorem records the alternative route taken in
CV18 itself: apply Lemma 7.15 directly to the chronological phase averages
stored by the executable history.  All structural obligations (ordering,
measurability, product identity, continuation-law identity, finite schedule
arithmetic, truncation, and the `13/64` base budget) are discharged here.

The remaining hypotheses are deliberately only the substantive statements
of Lemma 7.17(b,c): first/second moments of the executable phase averages and
approximate independence of the accumulated truncated product from the next
truncated phase average. -/

/-- Direct balanced-base assembly from the paper's finite chronological
moment and Lemma 7.17(c) premises.  This avoids the stronger full-history TV
replacement required by `balancedFigureOneBase_failure_le_of_phaseIteration`.
-/
theorem balancedFigureOneBase_failure_le_of_actualChronologicalMoments
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hrounded : WellRounded q I)
    (hW0 : ∀ j history,
      0 ≤ balancedCoolingChronologicalPhaseVariable q j history)
    (hWmem : ∀ j, MemLp
      (balancedCoolingChronologicalPhaseVariable q j) 2
      (balancedFigureOnePostInitialHistoryLaw parameters q I))
    (hWmean : ∀ j,
      (∫ history, balancedCoolingChronologicalPhaseVariable q j history
        ∂balancedFigureOnePostInitialHistoryLaw parameters q I) =
          figureOneChronologicalRawMean q I j)
    (hWsecond : ∀ j,
      (∫ history,
          balancedCoolingChronologicalPhaseVariable q j history ^ 2
        ∂balancedFigureOnePostInitialHistoryLaw parameters q I) ≤
          figureOneChronologicalMomentFactor q j *
            figureOneChronologicalRawMean q I j ^ 2)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (figureOneChronologicalTruncatedMean q I
            (balancedFigureOnePostInitialHistoryLaw parameters q I)
            (balancedCoolingChronologicalPhaseVariable q))
          (figureOneChronologicalTruncatedPhase q I
            (balancedCoolingChronologicalPhaseVariable q)) i)
        (figureOneChronologicalTruncatedPhase q I
          (balancedCoolingChronologicalPhaseVariable q) (i + 1))
        (balancedFigureOnePostInitialHistoryLaw parameters q I)) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
        explicitVolumeCoolingSchedule q).runEstimate oracle.query
          (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  let mu := balancedFigureOnePostInitialHistoryLaw parameters q I
  let W := balancedCoolingChronologicalPhaseVariable q
  let mean := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu W)
    (figureOneDependentPhaseCount q)
  let _ : IsProbabilityMeasure mu :=
    balancedFigureOnePostInitialHistoryLaw_isProbabilityMeasure parameters q I
  have hWmeas : ∀ j, Measurable (W j) :=
    fun j => measurable_balancedCoolingChronologicalPhaseVariable q j
  have htail := measure_chronologicalIdealPhaseSampleProduct_figureOne_le
    q I mu W hWmeas hW0 hWmem hWmean hWsecond hind
  have hmeanApprox :=
    figureOneChronologicalTruncatedMeanProduct_relativeApprox
      q I mu W hWmeas hW0 hWmem hWmean hWsecond
  have htransfer : MeasureLeUpTo
      (mu.map (fun history => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) history))
      (mu.map (fun history => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) history))
      (ENNReal.ofReal (1 / 64 : ℝ)) :=
    (MeasureLeUpTo.refl _).mono_error bot_le
  have hpost :=
    balancedFigureOnePostInitialDirectFailureBound_of_mappedProductLe
      parameters q I oracle (figureOneRadialTruncationBound q I hrounded)
      mu (dependentPhaseSampleProduct W (figureOneDependentPhaseCount q))
      (by
        unfold dependentPhaseSampleProduct
        exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
          fun j _ => hWmeas (j + 1))
      mean hmeanApprox htail
      (balancedFigureOnePostInitialHistoryLaw_ae_hasProduct parameters q I)
      htransfer
  exact balancedFigureOneBase_failure_le_of_directPostInitial
    parameters q I oracle hpost

/- The next four definitions use the executable history's own moments.  In
particular they do not assert that a finite walk has the exact stationary
mean; that quantitative comparison is kept visible in the final
`RelativeApprox` premise below. -/

noncomputable def balancedFigureOneActualRawMean
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  ∫ history, balancedCoolingChronologicalPhaseVariable q j history
    ∂balancedFigureOnePostInitialHistoryLaw parameters q I

noncomputable def balancedFigureOneActualTruncatedPhase
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    ℕ → Option (BalancedCoolingHistory q.n) → ℝ :=
  dependentTruncatedPhase (figureOneDependentAlpha q)
    (balancedFigureOneActualRawMean parameters q I)
    (balancedCoolingChronologicalPhaseVariable q)

noncomputable def balancedFigureOneActualTruncatedMean
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  ∫ history, balancedFigureOneActualTruncatedPhase parameters q I j history
    ∂balancedFigureOnePostInitialHistoryLaw parameters q I

noncomputable def balancedFigureOneActualTruncatedSecond
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (j : ℕ) : ℝ :=
  ∫ history,
      balancedFigureOneActualTruncatedPhase parameters q I j history ^ 2
    ∂balancedFigureOnePostInitialHistoryLaw parameters q I

/-- Fully law-correct specialization of Lemma 7.15.  Unlike the preceding
stationary-moment convenience theorem, the raw and truncated means here are
defined from the finite executable history law itself.  Thus all integral
identities are discharged by reflexivity.  The remaining hypotheses are
exactly the quantitative content needed from the paper's Lemma 7.17(b,c):
moment/truncation comparisons, product-center transfer, and adjacent-phase
approximate independence. -/
theorem balancedFigureOneBase_failure_le_of_lemma717bc
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (oracle : MembershipOracle I)
    (hrounded : WellRounded q I)
    (hW0 : ∀ j history,
      0 ≤ balancedCoolingChronologicalPhaseVariable q j history)
    (hWint : ∀ j, 1 ≤ j → j ≤ figureOneDependentPhaseCount q →
      Integrable (balancedCoolingChronologicalPhaseVariable q j)
        (balancedFigureOnePostInitialHistoryLaw parameters q I))
    (hmeanPos : ∀ j,
      0 < balancedFigureOneActualTruncatedMean parameters q I j)
    (hrawMeanPos : ∀ j,
      0 < balancedFigureOneActualRawMean parameters q I j)
    (hrawMean_le : ∀ j,
      balancedFigureOneActualRawMean parameters q I j ≤
        2 * balancedFigureOneActualTruncatedMean parameters q I j)
    (hmeanSecond : ∀ j,
      balancedFigureOneActualTruncatedMean parameters q I j ^ 2 ≤
        balancedFigureOneActualTruncatedSecond parameters q I j)
    (hrawSecond : ∀ j,
      balancedFigureOneActualRawMean parameters q I j ^ 2 ≤
        2 * balancedFigureOneActualTruncatedSecond parameters q I j)
    (hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (balancedFigureOneActualTruncatedMean parameters q I)
          (balancedFigureOneActualTruncatedPhase parameters q I) i)
        (balancedFigureOneActualTruncatedPhase parameters q I (i + 1))
        (balancedFigureOnePostInitialHistoryLaw parameters q I))
    (hrelative : ∀ i, i ≤ figureOneDependentPhaseCount q →
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 * i) *
          dependentPhaseMeanProduct
            (balancedFigureOneActualTruncatedSecond parameters q I) i ≤
        2 * dependentPhaseMeanProduct
          (balancedFigureOneActualTruncatedMean parameters q I) i ^ 2)
    (htailSecond :
      (1 + 2 * figureOneDependentEpsilon q *
          figureOneDependentAlpha q ^ 4 *
            figureOneDependentPhaseCount q) *
          dependentPhaseMeanProduct
            (balancedFigureOneActualTruncatedSecond parameters q I)
            (figureOneDependentPhaseCount q) ≤
        (1 + q.eps ^ 2 / 16) *
          dependentPhaseMeanProduct
            (balancedFigureOneActualTruncatedMean parameters q I)
            (figureOneDependentPhaseCount q) ^ 2)
    (hmeanApprox : RelativeApprox (q.eps / 32)
      (∏ phase, figureOneIdealPhaseMean q I phase)
      (dependentPhaseMeanProduct
        (balancedFigureOneActualTruncatedMean parameters q I)
        (figureOneDependentPhaseCount q))) :
    (baseVolumeCooling (balancedCoolingPrimitives parameters)
        explicitVolumeCoolingSchedule q).runEstimate oracle.query
          (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  let mu := balancedFigureOnePostInitialHistoryLaw parameters q I
  let W := balancedCoolingChronologicalPhaseVariable q
  let rawMean := balancedFigureOneActualRawMean parameters q I
  let V := balancedFigureOneActualTruncatedPhase parameters q I
  let mean := balancedFigureOneActualTruncatedMean parameters q I
  let second := balancedFigureOneActualTruncatedSecond parameters q I
  let _ : IsProbabilityMeasure mu :=
    balancedFigureOnePostInitialHistoryLaw_isProbabilityMeasure parameters q I
  have hWmeas : ∀ j, Measurable (W j) :=
    fun j => measurable_balancedCoolingChronologicalPhaseVariable q j
  have hVmeas : ∀ j, Measurable (V j) := by
    intro j
    exact (hWmeas j).min measurable_const
  have hV0 : ∀ j history, 0 ≤ V j history := by
    intro j history
    exact le_min (hW0 j history)
      (mul_nonneg (figureOneDependentAlpha_pos q).le
        (hrawMeanPos j).le)
  have hVcap : ∀ j history,
      V j history ≤ figureOneDependentAlpha q * rawMean j := by
    intro j history
    exact min_le_right _ _
  have htail := measure_dependentPhaseSampleProduct_figureOne_le
    q mu mean rawMean second V W
      (fun j => (hmeanPos j).le) hmeanPos
      (fun j => (hrawMeanPos j).le) hrawMeanPos hrawMean_le
      (fun j => (sq_nonneg (mean j)).trans (hmeanSecond j))
      hmeanSecond hrawSecond hVmeas hV0 hVcap
      (fun _ => rfl) (fun _ => rfl)
      (fun _ _ _ _ => rfl)
      (fun j _ _ => hWmeas j) (fun j _ _ => hW0 j)
      hWint (fun _ _ _ => rfl) hind hrelative htailSecond
  have htransfer : MeasureLeUpTo
      (mu.map (fun history => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) history))
      (mu.map (fun history => initialGaussianIntegral q *
        dependentPhaseSampleProduct W
          (figureOneDependentPhaseCount q) history))
      (ENNReal.ofReal (1 / 64 : ℝ)) :=
    (MeasureLeUpTo.refl _).mono_error bot_le
  have hpost :=
    balancedFigureOnePostInitialDirectFailureBound_of_mappedProductLe
      parameters q I oracle (figureOneRadialTruncationBound q I hrounded)
      mu (dependentPhaseSampleProduct W (figureOneDependentPhaseCount q))
      (by
        unfold dependentPhaseSampleProduct
        exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
          fun j _ => hWmeas (j + 1))
      (dependentPhaseMeanProduct mean (figureOneDependentPhaseCount q))
      hmeanApprox htail
      (balancedFigureOnePostInitialHistoryLaw_ae_hasProduct parameters q I)
      htransfer
  exact balancedFigureOneBase_failure_le_of_directPostInitial
    parameters q I oracle hpost

#print axioms MeasureLeUpTo.map_iteratedKernelLaw_of_figureOne_phase_max
#print axioms figureOnePhaseReplacementBudget_sum_le
#print axioms MeasureLeUpTo.map_figureOnePhaseIteration
#print axioms balancedFigureOneBase_failure_le_of_phaseIteration
#print axioms balancedFigureOneBase_failure_le_of_actualChronologicalMoments
#print axioms balancedFigureOneBase_failure_le_of_lemma717bc

end

end ArlibCommunity.Algorithms.CV18
