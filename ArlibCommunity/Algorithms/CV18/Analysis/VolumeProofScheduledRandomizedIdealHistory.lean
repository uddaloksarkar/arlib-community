/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledChronologicalPhase

/-!
# Randomized ideal chronological history laws

The chronological comparison state used earlier in the development carries a
complete ideal experiment beside the visible history.  That representation is
convenient for proving the final product identity, but it is too strong for a
one-phase replacement theorem: the next ideal history is visibly correlated
with the carried experiment, whereas the executable phase uses fresh
randomness.

This file projects away the carried experiment before every replacement.  The
resulting sequence of history laws is exactly the law of successively appending
fresh independent ideal phase blocks.  Exact-chance induction only needs this
sequence of measures and its one-step replacement estimates; no pointwise
ideal kernel on a state containing future randomness is required.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Exact-chance induction against an explicitly supplied sequence of ideal
prefix laws.  This is the law-sequence form of
`MeasureLeUpTo.iteratedKernelLaw_exactChance`. -/
theorem MeasureLeUpTo.iteratedKernelLaw_le_lawSequence
    {S : Type*} [MeasurableSpace S]
    (actualK : ℕ → S → Measure S) (actualInitial : Measure S)
    (idealLaw : ℕ → Measure S) {nu : ENNReal}
    (hinitial : MeasureLeUpTo actualInitial (idealLaw 0) 0)
    (hactualMeas : ∀ i, Measurable (actualK i))
    (hactualProb : ∀ i state, IsProbabilityMeasure (actualK i state))
    (t : ℕ)
    (hstep : ∀ i, i < t →
      MeasureLeUpTo ((idealLaw i).bind (actualK i)) (idealLaw (i + 1)) nu) :
    MeasureLeUpTo
      (iteratedKernelLaw actualK actualInitial t) (idealLaw t) (t • nu) := by
  induction t with
  | zero => simpa using hinitial
  | succ t ih =>
      have ih' := ih fun i hi => hstep i (hi.trans (Nat.lt_succ_self t))
      have hnext := MeasureLeUpTo.bind_then_replace ih' (actualK t)
        (hactualMeas t) (hactualProb t) (hstep t (Nat.lt_succ_self t))
      simpa only [iteratedKernelLaw_succ, succ_nsmul] using hnext

/-- The ideal chronological prefix after future ideal randomness has been
projected away.  Distributionally, this is the history obtained by drawing a
fresh independent ideal block at each completed phase. -/
noncomputable def figureOneRandomizedIdealHistoryLaw
    (q : VolumeParams) (I : VolumeInput q.n) (phases : ℕ) :
    Measure (Option (BalancedCoolingHistory q.n)) :=
  (iteratedKernelLaw (figureOneIdealChronologicalPhaseKernel q)
    (scheduledChronologicalCommonInitial q I) phases).map Prod.snd

theorem figureOneRandomizedIdealHistoryLaw_isProbabilityMeasure
    (q : VolumeParams) (I : VolumeInput q.n) (phases : ℕ) :
    IsProbabilityMeasure (figureOneRandomizedIdealHistoryLaw q I phases) := by
  let idealInitial := scheduledChronologicalCommonInitial q I
  let _ : IsProbabilityMeasure (figureOneIdealExperimentLaw q I) :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  let initialHistory :=
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        balancedCoolingInitialHistory
  let _ : IsProbabilityMeasure initialHistory :=
    Measure.isProbabilityMeasure_map
      measurable_balancedCoolingInitialHistory.aemeasurable
  let _ : IsProbabilityMeasure idealInitial := by
    dsimp [idealInitial, scheduledChronologicalCommonInitial]
    infer_instance
  let _ : IsProbabilityMeasure
      (iteratedKernelLaw (figureOneIdealChronologicalPhaseKernel q)
        idealInitial phases) :=
    iteratedKernelLaw_isProbabilityMeasure
      (figureOneIdealChronologicalPhaseKernel q) idealInitial inferInstance
      (fun phase =>
        (figureOneIdealChronologicalPhaseKernel_measurable_and_probability
          q phase).1)
      (fun phase state =>
        (figureOneIdealChronologicalPhaseKernel_measurable_and_probability
          q phase).2 state)
      phases
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

theorem figureOneRandomizedIdealHistoryLaw_zero
    (q : VolumeParams) (I : VolumeInput q.n) :
    figureOneRandomizedIdealHistoryLaw q I 0 =
      (truncatedGaussianProbability q I (initialVariance q)
        (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
          balancedCoolingInitialHistory := by
  simpa [figureOneRandomizedIdealHistoryLaw] using
    scheduledChronologicalCommonInitial_map_snd q I

/-- Projecting away the latent ideal experiment retains the already-proved
ideal scalar product law. -/
theorem figureOneRandomizedIdealHistoryLaw_map_output
    (q : VolumeParams) (I : VolumeInput q.n) :
    (figureOneRandomizedIdealHistoryLaw q I
      (figureOneDependentPhaseCount q)).map
        (balancedFigureOneHistoryEstimate q) =
      (figureOneIdealExperimentLaw q I).map
        (fun samples => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (figureOneChronologicalIdealCoordinate q)
            (figureOneDependentPhaseCount q) samples) := by
  rw [figureOneRandomizedIdealHistoryLaw, Measure.map_map
    (measurable_balancedFigureOneHistoryEstimate q) measurable_snd]
  exact figureOneIdealChronologicalIteration_map_output q I

/-- Correct outer exact-chance transfer on history alone.  Its premise is a
complete-phase replacement integrated against the randomized ideal prefix,
so it cannot inspect or correlate with unused future ideal samples. -/
theorem MeasureLeUpTo.map_scheduledHistory_le_randomizedIdeal
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n)
    (hphase : ∀ phase, phase < figureOneDependentPhaseCount q →
      MeasureLeUpTo
        ((figureOneRandomizedIdealHistoryLaw q I phase).bind
          (scheduledBalancedForwardPhaseKernel parameters q I phase))
        (figureOneRandomizedIdealHistoryLaw q I (phase + 1))
        (figureOnePhaseReplacementBudget q)) :
    MeasureLeUpTo
      ((scheduledBalancedForwardHistoryLaw parameters q I
        (figureOneDependentPhaseCount q)).map
          (balancedFigureOneHistoryEstimate q))
      ((figureOneIdealExperimentLaw q I).map
        (fun samples => initialGaussianIntegral q *
          dependentPhaseSampleProduct
            (figureOneChronologicalIdealCoordinate q)
            (figureOneDependentPhaseCount q) samples))
      (ENNReal.ofReal (1 / 64 : ℝ)) := by
  let actualK := scheduledBalancedForwardPhaseKernel parameters q I
  let actualInitial :=
    (truncatedGaussianProbability q I (initialVariance q)
      (initialVariance_pos q) : Measure (AmbientSpace q.n)).map
        balancedCoolingInitialHistory
  let idealLaw := figureOneRandomizedIdealHistoryLaw q I
  have hhistory := MeasureLeUpTo.iteratedKernelLaw_le_lawSequence
    actualK actualInitial idealLaw
      (by
        rw [show idealLaw 0 = actualInitial by
          simpa [idealLaw, actualInitial] using
            figureOneRandomizedIdealHistoryLaw_zero q I]
        exact MeasureLeUpTo.refl actualInitial)
      (fun phase =>
        (scheduledBalancedForwardPhaseKernel_measurable_and_probability
          parameters q I phase).1)
      (fun phase history =>
        (scheduledBalancedForwardPhaseKernel_measurable_and_probability
          parameters q I phase).2 history)
      (figureOneDependentPhaseCount q)
      (fun phase hp => by simpa [idealLaw, actualK] using hphase phase hp)
  have hmapped := hhistory.map
    (measurable_balancedFigureOneHistoryEstimate q)
  have hbudget := figureOnePhaseReplacementBudget_sum_le q
  rw [show iteratedKernelLaw actualK actualInitial
        (figureOneDependentPhaseCount q) =
      scheduledBalancedForwardHistoryLaw parameters q I
        (figureOneDependentPhaseCount q) by rfl,
    figureOneRandomizedIdealHistoryLaw_map_output q I] at hmapped
  exact hmapped.mono_error hbudget

/-- Post-initial accuracy capstone with the corrected, history-only ideal
prefix premise. -/
theorem scheduledPostInitialDirectFailureBound_of_randomizedIdealHistory
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (hrounded : WellRounded q I)
    (continuation : AmbientSpace q.n → Measure ℝ)
    (hlaw :
      (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          continuation =
        (scheduledBalancedForwardHistoryLaw parameters q I
          (figureOneDependentPhaseCount q)).map
            (balancedFigureOneHistoryEstimate q))
    (hphase : ∀ phase, phase < figureOneDependentPhaseCount q →
      MeasureLeUpTo
        ((figureOneRandomizedIdealHistoryLaw q I phase).bind
          (scheduledBalancedForwardPhaseKernel parameters q I phase))
        (figureOneRandomizedIdealHistoryLaw q I (phase + 1))
        (figureOnePhaseReplacementBudget q)) :
    FigureOnePostInitialDirectFailureBoundFor q I continuation := by
  have htransfer := MeasureLeUpTo.map_scheduledHistory_le_randomizedIdeal
    parameters q I hphase
  let W := figureOneChronologicalIdealCoordinate q
  let mu := figureOneIdealExperimentLaw q I
  let mean := dependentPhaseMeanProduct
    (figureOneChronologicalTruncatedMean q I mu W)
    (figureOneDependentPhaseCount q)
  let _ : IsProbabilityMeasure mu :=
    figureOneIdealExperimentLaw_isProbabilityMeasure q I
  have hmeas : ∀ j, Measurable (W j) :=
    fun j => figureOneChronologicalIdealCoordinate_measurable q j
  have hnonneg : ∀ j samples, 0 ≤ W j samples :=
    fun j samples => figureOneChronologicalIdealCoordinate_nonneg q j samples
  have hmem : ∀ j, MemLp (W j) 2 mu :=
    fun j => figureOneChronologicalIdealCoordinate_memLp q I j 2
  have hsharp := figureOneSharpAcceleratedMoments q I
  have hmean : ∀ j, (∫ samples, W j samples ∂mu) =
      figureOneChronologicalRawMean q I j :=
    fun j => figureOneChronologicalIdealCoordinate_mean q I hsharp j
  have hsecond : ∀ j, (∫ samples, W j samples ^ 2 ∂mu) ≤
      figureOneChronologicalMomentFactor q j *
        figureOneChronologicalRawMean q I j ^ 2 :=
    fun j => figureOneChronologicalIdealCoordinate_secondMoment_le
      q I hsharp j
  have hind : ∀ i, i < figureOneDependentPhaseCount q →
      ApproxIndepFun (figureOneDependentEpsilon q)
        (dependentTruncatedProduct (figureOneDependentAlpha q)
          (figureOneChronologicalTruncatedMean q I mu W)
          (figureOneChronologicalTruncatedPhase q I W) i)
        (figureOneChronologicalTruncatedPhase q I W (i + 1)) mu := by
    intro i hi
    exact (figureOneChronologicalIdeal_exactIndependence q I i hi).mono
      (figureOneDependentEpsilon_nonneg q)
  have htail := measure_chronologicalIdealPhaseSampleProduct_figureOne_le
    q I mu W hmeas hnonneg hmem hmean hsecond hind
  have hmeanApprox :=
    figureOneChronologicalTruncatedMeanProduct_relativeApprox
      q I mu W hmeas hnonneg hmem hmean hsecond
  have hestimate : balancedFigureOneHistoryEstimate q = fun history =>
      initialGaussianIntegral q * balancedCoolingHistoryProduct q history := by
    funext history
    cases history <;>
      simp [balancedFigureOneHistoryEstimate, balancedCoolingHistoryProduct]
  rw [hestimate] at htransfer hlaw
  apply figureOnePostInitialDirectFailureBoundFor_of_mappedProductLe
    q I continuation (figureOneRadialTruncationBound q I hrounded)
    (scheduledBalancedForwardHistoryLaw parameters q I
      (figureOneDependentPhaseCount q)) mu
    (balancedCoolingHistoryProduct q)
    (dependentPhaseSampleProduct W (figureOneDependentPhaseCount q))
    (measurable_balancedCoolingHistoryProduct q)
    (by
      unfold dependentPhaseSampleProduct
      exact (Finset.range (figureOneDependentPhaseCount q)).measurable_fun_prod
        fun j _ => hmeas (j + 1))
    mean hmeanApprox htail
  · simpa [W, mu] using htransfer
  · exact hlaw

/-- Final balanced-base wrapper for the corrected randomized ideal-prefix
route.  Once the history-only phase replacement is supplied, no executable
raw second-moment premise remains. -/
theorem figureOneFinalScheduledBalancedBase_failure_le_of_postHistory_randomizedIdeal
    (q : VolumeParams) (I : VolumeInput q.n)
    (oracle : MembershipOracle I) (hrounded : WellRounded q I)
    (hpostLaw :
      (truncatedGaussianProbability q I (initialVariance q)
          (initialVariance_pos q) : Measure (AmbientSpace q.n)).bind
          (fun point =>
            (scheduledBalancedFigureOnePointContinuation
              figureOneFinalScheduledBalancedParameters q point).runEstimate
                oracle.query) =
        (scheduledBalancedForwardHistoryLaw
          figureOneFinalScheduledBalancedParameters q I
          (figureOneDependentPhaseCount q)).map
            (balancedFigureOneHistoryEstimate q))
    (hphase : ∀ phase, phase < figureOneDependentPhaseCount q →
      MeasureLeUpTo
        ((figureOneRandomizedIdealHistoryLaw q I phase).bind
          (scheduledBalancedForwardPhaseKernel
            figureOneFinalScheduledBalancedParameters q I phase))
        (figureOneRandomizedIdealHistoryLaw q I (phase + 1))
        (figureOnePhaseReplacementBudget q)) :
    (figureOneFinalScheduledBalancedBaseProgram q).runEstimate oracle.query
        (accurateOutcome q I)ᶜ ≤ ENNReal.ofReal (13 / 64 : ℝ) := by
  have hpost :=
    scheduledPostInitialDirectFailureBound_of_randomizedIdealHistory
      figureOneFinalScheduledBalancedParameters q I hrounded
      (fun point =>
        (scheduledBalancedFigureOnePointContinuation
          figureOneFinalScheduledBalancedParameters q point).runEstimate
            oracle.query)
      hpostLaw hphase
  exact figureOneFinalScheduledBalancedBase_failure_le_of_directPostInitial
    q I oracle hpost

#print axioms MeasureLeUpTo.iteratedKernelLaw_le_lawSequence
#print axioms figureOneRandomizedIdealHistoryLaw_isProbabilityMeasure
#print axioms figureOneRandomizedIdealHistoryLaw_zero
#print axioms figureOneRandomizedIdealHistoryLaw_map_output
#print axioms MeasureLeUpTo.map_scheduledHistory_le_randomizedIdeal
#print axioms
  scheduledPostInitialDirectFailureBound_of_randomizedIdealHistory
#print axioms
  figureOneFinalScheduledBalancedBase_failure_le_of_postHistory_randomizedIdeal

end

end ArlibCommunity.Algorithms.CV18
