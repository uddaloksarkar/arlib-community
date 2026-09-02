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

#print axioms MeasureLeUpTo.map_iteratedKernelLaw_of_figureOne_phase_max
#print axioms figureOnePhaseReplacementBudget_sum_le
#print axioms MeasureLeUpTo.map_figureOnePhaseIteration
#print axioms balancedFigureOneBase_failure_le_of_phaseIteration

end

end ArlibCommunity.Algorithms.CV18
