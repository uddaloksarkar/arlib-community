/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGoodBadIndependence
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceDependentAssembly

/-! # Full retained-state good/bad decomposition for the scheduled trace -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Set
open _root_.Arlib _root_.Arlib.MarkovChains

/-! ## The asymmetric form of Lemma 7.17(b) -/

/-- In the good/bad trace argument the conditioned next-phase law pays twice
the accumulated bad mass, whereas the unconditional law pays it only once.
Keeping those two errors separate is essential: replacing both by the larger
one loses a factor four and no longer fits CV18's `3 k m nu` allocation. -/
theorem approxIndepFun_sequentialPairLaw_of_asymmetric_leUpTo
    {H T : Type*} [MeasurableSpace H] [MeasurableSpace T]
    (rho : Measure H) [IsProbabilityMeasure rho]
    (K : H → Measure T) (hK : Measurable K)
    (hKprob : ∀ h, IsProbabilityMeasure (K h))
    (target : Measure T) [IsProbabilityMeasure target]
    {conditionedError baseError : ENNReal}
    (hconditionedTop : conditionedError ≠ ⊤)
    (hbaseTop : baseError ≠ ⊤)
    (hconditioned : ∀ mu : Measure H, IsProbabilityMeasure mu →
      Arlib.IsWarm 2 mu rho →
      MeasureLeUpTo (mu.bind K) target conditionedError)
    (hbase : MeasureLeUpTo (rho.bind K) target baseError) :
    ApproxIndepFun (conditionedError + baseError).toReal
      Prod.fst Prod.snd (sequentialPairLaw rho K) := by
  apply approxIndepFun_fst_snd_sequentialPairLaw_of_condOn_bind_tv
    rho hK hKprob (ENNReal.add_ne_top.mpr
      ⟨hconditionedTop, hbaseTop⟩)
  intro A hA hhalf
  have hAposReal : 0 < rho.real A :=
    lt_of_lt_of_le (by norm_num) hhalf
  have hA0 : rho A ≠ 0 := by
    intro hzero
    rw [measureReal_def, hzero] at hAposReal
    simp at hAposReal
  let hcondProb : IsProbabilityMeasure (Arlib.condOn rho A) :=
    Arlib.isProbabilityMeasure_condOn rho hA0 (measure_ne_top rho A)
  let _ : IsProbabilityMeasure (Arlib.condOn rho A) := hcondProb
  let _ : IsProbabilityMeasure ((Arlib.condOn rho A).bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hKprob)
  let _ : IsProbabilityMeasure (rho.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hKprob)
  have hleft := hconditioned (Arlib.condOn rho A) hcondProb
    (isWarm_condOn_two_of_half rho hA hhalf)
  exact hleft.to_tvLe.trans hbase.to_tvLe.symm

/-! ## Exact arithmetic of the accumulated retained error -/

theorem figureOneScheduledRetainedError_toReal_le
    (q : VolumeParams) (phases : ℕ) :
    (figureOneScheduledRetainedError q phases).toReal ≤
      figureOnePerSampleMixingError q / 4 +
        (phases : ℝ) * (figureOneDependentMaxSampleCount q : ℝ) *
          figureOnePerSampleMixingError q := by
  have hnu : 0 ≤ figureOnePerSampleMixingError q :=
    (figureOnePerSampleMixingError_pos q).le
  have htarget := scheduledBalancedStationaryTargetError_le_targetBudget q
  have htargetBudgetTop : figureOneCorrectedTargetBudget q ≠ ⊤ := by
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have htargetTop : scheduledBalancedStationaryTargetError q ≠ ⊤ :=
    ne_top_of_le_ne_top htargetBudgetTop htarget
  have htermTop : ∀ phase,
      figureOnePhaseSampleCount q (scheduleValue q phase) •
          figureOneCorrectedTransitionBudget q ≠ ⊤ := by
    intro phase
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top
  have hsumTop : (∑ phase ∈ Finset.range phases,
      figureOnePhaseSampleCount q (scheduleValue q phase) •
        figureOneCorrectedTransitionBudget q) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.2 fun phase _ => htermTop phase
  rw [figureOneScheduledRetainedError,
    ENNReal.toReal_add htargetTop hsumTop]
  calc
    (scheduledBalancedStationaryTargetError q).toReal +
        (∑ phase ∈ Finset.range phases,
          figureOnePhaseSampleCount q (scheduleValue q phase) •
            figureOneCorrectedTransitionBudget q).toReal ≤
      (figureOneCorrectedTargetBudget q).toReal +
        ∑ phase ∈ Finset.range phases,
          (figureOnePhaseSampleCount q (scheduleValue q phase) : ℝ) *
            figureOnePerSampleMixingError q := by
      apply add_le_add
      · exact ENNReal.toReal_mono htargetBudgetTop htarget
      · rw [ENNReal.toReal_sum fun phase _ => htermTop phase]
        apply Finset.sum_le_sum
        intro phase hphase
        rw [ENNReal.toReal_nsmul,
          figureOneCorrectedTransitionBudget,
          ENNReal.toReal_ofReal hnu]
        simp [nsmul_eq_mul]
    _ ≤ figureOnePerSampleMixingError q / 4 +
        ∑ _phase ∈ Finset.range phases,
          (figureOneDependentMaxSampleCount q : ℝ) *
            figureOnePerSampleMixingError q := by
      apply add_le_add
      · simp [figureOneCorrectedTargetBudget,
          figureOneCorrectedTransitionBudget, ENNReal.toReal_div,
          ENNReal.toReal_ofReal hnu]
      · apply Finset.sum_le_sum
        intro phase hphase
        have hcount :
            (figureOnePhaseSampleCount q (scheduleValue q phase) : ℝ) ≤
              (figureOneDependentMaxSampleCount q : ℝ) := by
          exact_mod_cast figureOnePhaseSampleCount_le_dependentMax
            q (scheduleValue q phase)
        exact mul_le_mul_of_nonneg_right hcount hnu
    _ = figureOnePerSampleMixingError q / 4 +
        (phases : ℝ) * (figureOneDependentMaxSampleCount q : ℝ) *
          figureOnePerSampleMixingError q := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- The asymmetric conditioned/unconditioned comparison fits exactly inside
the paper's dependence budget at every noninitial chronological phase. -/
theorem figureOneScheduledRetained_asymmetric_budget
    (q : VolumeParams) (phases : ℕ)
    (hphases : phases < figureOneDependentPhaseCount q) :
    ((figureOneCorrectedTransitionBudget q +
          2 * figureOneScheduledRetainedError q phases) +
        (figureOneCorrectedTransitionBudget q +
          figureOneScheduledRetainedError q phases)).toReal ≤
      figureOneDependentEpsilon q := by
  have hnu : 0 < figureOnePerSampleMixingError q :=
    figureOnePerSampleMixingError_pos q
  have herrTop : figureOneScheduledRetainedError q phases ≠ ⊤ := by
    unfold figureOneScheduledRetainedError
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ne_top_of_le_ne_top
        (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num))
        (scheduledBalancedStationaryTargetError_le_targetBudget q)
    · exact ENNReal.sum_ne_top.2 fun phase _ => by
        rw [nsmul_eq_mul]
        exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          ENNReal.ofReal_ne_top
  have hbudgetReal := figureOneScheduledRetainedError_toReal_le q phases
  have htransitionTop : figureOneCorrectedTransitionBudget q ≠ ⊤ := by
    simp [figureOneCorrectedTransitionBudget]
  have htwoErrorTop : 2 * figureOneScheduledRetainedError q phases ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) herrTop
  have hreal :
      ((figureOneCorrectedTransitionBudget q +
            2 * figureOneScheduledRetainedError q phases) +
          (figureOneCorrectedTransitionBudget q +
            figureOneScheduledRetainedError q phases)).toReal =
        2 * figureOnePerSampleMixingError q +
          3 * (figureOneScheduledRetainedError q phases).toReal := by
    rw [ENNReal.toReal_add
        (ENNReal.add_ne_top.mpr ⟨htransitionTop, htwoErrorTop⟩)
        (ENNReal.add_ne_top.mpr ⟨htransitionTop, herrTop⟩),
      ENNReal.toReal_add htransitionTop htwoErrorTop,
      ENNReal.toReal_add htransitionTop herrTop,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      figureOneCorrectedTransitionBudget,
      ENNReal.toReal_ofReal hnu.le]
    ring
  rw [hreal]
  have hphaseCast : (phases : ℝ) + 1 ≤
      figureOneDependentPhaseCount q := by
    exact_mod_cast (Nat.succ_le_iff.mpr hphases)
  have hk : (1 : ℝ) ≤ figureOneDependentMaxSampleCount q := by
    exact_mod_cast figureOneDependentMaxSampleCount_pos q
  have hphaseProduct := mul_le_mul_of_nonneg_right hphaseCast
    (mul_nonneg
      (show 0 ≤ (figureOneDependentMaxSampleCount q : ℝ) by positivity)
      hnu.le)
  have hnuProduct := mul_le_mul_of_nonneg_right hk hnu.le
  rw [← figureOne_lemma717c_budget q]
  nlinarith [hphaseProduct, hnuProduct]

/-! ## Completing only the live subprobability -/

/-- A subprobability dominated by a warm good part and a bad part can be
completed to a warm probability measure while charging only the bad part.
Unlike completing the full live/dead state marginal, this leaves the dead
mass available for its actual absorbing output. -/
theorem exists_warm_probability_of_submeasure_le_good_add_bad
    {Omega : Type*} [MeasurableSpace Omega]
    (sub good bad pi : Measure Omega)
    [IsFiniteMeasure sub] [IsFiniteMeasure bad] [IsProbabilityMeasure pi]
    {M : ENNReal} (hM : 1 ≤ M) (hMtop : M ≠ ⊤)
    (hsubMass : sub Set.univ ≤ 1)
    (hsub : sub ≤ good + bad) (hgood : Arlib.IsWarm M good pi) :
    ∃ nu : Measure Omega, IsProbabilityMeasure nu ∧
      Arlib.IsWarm M nu pi ∧ sub ≤ nu + bad := by
  let residual := sub - bad
  have hresidualLeGood : residual ≤ good :=
    Measure.sub_le_of_le_add hsub
  have hgoodLe : good ≤ M • pi :=
    (isWarm_iff_le_smul good pi).1 hgood
  have hresidualLe : residual ≤ M • pi :=
    hresidualLeGood.trans hgoodLe
  have hresidualMass : residual Set.univ ≤ 1 :=
    (Measure.le_iff'.mp (Measure.sub_le (μ := sub) (ν := bad))
      Set.univ).trans hsubMass
  let missing := 1 - residual Set.univ
  let capacity := M • pi - residual
  have hcapacityMass : capacity Set.univ = M - residual Set.univ := by
    rw [show capacity = M • pi - residual by rfl,
      Measure.sub_apply MeasurableSet.univ hresidualLe,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  have hmissingLeCapacity : missing ≤ capacity Set.univ := by
    rw [hcapacityMass]
    exact tsub_le_tsub_right hM (residual Set.univ)
  by_cases hmissing0 : missing = 0
  · refine ⟨residual, ?_, ?_, ?_⟩
    · refine ⟨?_⟩
      apply le_antisymm hresidualMass
      exact (tsub_eq_zero_iff_le).mp hmissing0
    · exact (isWarm_iff_le_smul residual pi).2 hresidualLe
    · exact (Measure.sub_le_iff_le_add (μ := sub) (ν := bad)
        (ξ := residual)).mp le_rfl
  · have hcapacity0 : capacity Set.univ ≠ 0 := by
      intro hzero
      apply hmissing0
      apply bot_unique
      simpa [hzero] using hmissingLeCapacity
    have hcapacityTop : capacity Set.univ ≠ ⊤ := by
      rw [hcapacityMass]
      exact ne_top_of_le_ne_top hMtop tsub_le_self
    let coefficient := missing / capacity Set.univ
    have hcoefficientLe : coefficient ≤ 1 :=
      ENNReal.div_le_iff_le_mul (Or.inl hcapacity0)
        (Or.inl hcapacityTop) |>.2 <| by
          simpa using hmissingLeCapacity
    let filler := coefficient • capacity
    let nu := residual + filler
    have hfillerLe : filler ≤ capacity := by
      apply Measure.le_iff'.mpr
      intro S
      rw [show filler = coefficient • capacity by rfl,
        Measure.smul_apply, smul_eq_mul]
      exact mul_le_of_le_one_left bot_le hcoefficientLe
    have hnuLe : nu ≤ M • pi := by
      calc
        nu = residual + filler := rfl
        _ ≤ residual + capacity := by gcongr
        _ = M • pi := by
          rw [show capacity = M • pi - residual by rfl, add_comm,
            Measure.sub_add_cancel_of_le hresidualLe]
    have hfillerMass : filler Set.univ = missing := by
      rw [show filler = coefficient • capacity by rfl,
        Measure.smul_apply, smul_eq_mul]
      exact ENNReal.div_mul_cancel hcapacity0 hcapacityTop
    have hnuMass : nu Set.univ = 1 := by
      rw [show nu = residual + filler by rfl, Measure.add_apply,
        hfillerMass, show missing = 1 - residual Set.univ by rfl]
      exact add_tsub_cancel_of_le hresidualMass
    let hnuProb : IsProbabilityMeasure nu := ⟨hnuMass⟩
    refine ⟨nu, hnuProb, (isWarm_iff_le_smul nu pi).2 hnuLe, ?_⟩
    calc
      sub ≤ residual + bad :=
        (Measure.sub_le_iff_le_add (μ := sub) (ν := bad)
          (ξ := residual)).mp le_rfl
      _ ≤ nu + bad := by
        gcongr
        exact Measure.le_add_right le_rfl

/-- Run a common transition on the live submeasure and emit an arbitrary
probability output on the absorbing dead mass.  The warm completion above
shows that the total additive loss is the transition budget plus the sum of
the live bad mass and dead mass, with neither charged twice. -/
theorem measureLeUpTo_live_dead_bind_of_good_bad
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (live dead good bad pi : Measure S)
    [IsFiniteMeasure live] [IsFiniteMeasure dead] [IsFiniteMeasure bad]
    [IsProbabilityMeasure pi]
    {M eta budget : ENNReal} (hM : 1 ≤ M) (hMtop : M ≠ ⊤)
    (hmass : live Set.univ + dead Set.univ = 1)
    (hlive : live ≤ good + bad) (hgood : Arlib.IsWarm M good pi)
    (herror : bad Set.univ + dead Set.univ ≤ eta)
    (K : S → Measure T) (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (deadOutput target : Measure T) [IsProbabilityMeasure deadOutput]
    [IsProbabilityMeasure target]
    (hmix : ∀ nu : Measure S, IsProbabilityMeasure nu →
      Arlib.IsWarm M nu pi →
      MeasureLeUpTo (nu.bind K) target budget) :
    MeasureLeUpTo
      (live.bind K + dead Set.univ • deadOutput) target (budget + eta) := by
  have hliveMass : live Set.univ ≤ 1 := by
    calc
      live Set.univ ≤ live Set.univ + dead Set.univ := le_add_right le_rfl
      _ = 1 := hmass
  obtain ⟨nu, hnuProb, hnuWarm, hliveNu⟩ :=
    exists_warm_probability_of_submeasure_le_good_add_bad
      live good bad pi hM hMtop hliveMass hlive hgood
  let _ : IsProbabilityMeasure nu := hnuProb
  obtain ⟨mixError, hmixDom, hmixMass⟩ := hmix nu hnuProb hnuWarm
  let error := mixError + bad.bind K + dead Set.univ • deadOutput
  refine ⟨error, ?_, ?_⟩
  · have hbind := measure_bind_mono_left hliveNu hK
    rw [measure_bind_add_left nu bad hK] at hbind
    calc
      live.bind K + dead Set.univ • deadOutput ≤
          (nu.bind K + bad.bind K) + dead Set.univ • deadOutput := by
        gcongr
      _ ≤ (target + mixError + bad.bind K) +
          dead Set.univ • deadOutput := by
        gcongr
      _ = target + error := by
        simp only [error]
        ac_rfl
  · rw [show error = mixError + bad.bind K +
        dead Set.univ • deadOutput by rfl,
      Measure.add_apply, Measure.add_apply,
      measure_bind_apply_univ bad hK hKprob,
      Measure.smul_apply, smul_eq_mul]
    have hdeadOutputMass : deadOutput Set.univ = 1 := measure_univ
    rw [hdeadOutputMass, mul_one]
    calc
      mixError Set.univ + bad Set.univ + dead Set.univ =
          mixError Set.univ + (bad Set.univ + dead Set.univ) := by
        ac_rfl
      _ ≤ budget + eta := add_le_add hmixMass herror

/-! ## The actual live/dead phase law -/

/-- A Gaussian phase kernel whose input is already in the speedy (scaled)
coordinates used by the scheduled walk. -/
noncomputable def figureOneScheduledScaledGaussianPhaseLaw
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    AmbientSpace q.n → Measure (Option (ℝ × AmbientSpace q.n)) :=
  fun current =>
    (scheduledBalancedTransitionCollectLaw q I (scheduleValue q phase)
      (gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase))
      (figureOnePhaseSampleCount q (scheduleValue q phase)) 0 current).map
        (balancedCoolingAverage
          (figureOnePhaseSampleCount q (scheduleValue q phase)))

theorem figureOneScheduledScaledGaussianPhaseLaw_measurable_and_probability
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    Measurable (figureOneScheduledScaledGaussianPhaseLaw q I phase) ∧
    ∀ current, IsProbabilityMeasure
      (figureOneScheduledScaledGaussianPhaseLaw q I phase current) := by
  let count := figureOnePhaseSampleCount q (scheduleValue q phase)
  have hcollect :=
    scheduledBalancedTransitionCollectLaw_measurable_and_probability
      q I (scheduleValue_pos q phase)
      (measurable_gaussianRatioWeight (scheduleValue q phase)
        (scheduleValue q (phase + 1)))
      (figureOneFinalScheduledBalancedParameters.proposalCap q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.properStride q
        (scheduleValue q phase))
      (figureOneFinalScheduledBalancedParameters.retryLimit q
        (scheduleValue q phase)) count
  have havg := measurable_balancedCoolingAverage (n := q.n) count
  constructor
  · unfold figureOneScheduledScaledGaussianPhaseLaw
    exact (Measure.measurable_map _ havg).comp <|
      hcollect.1.comp (measurable_const.prodMk measurable_id)
  · intro current
    unfold figureOneScheduledScaledGaussianPhaseLaw
    let _ : IsProbabilityMeasure
        (scheduledBalancedTransitionCollectLaw q I (scheduleValue q phase)
          (gaussianRatioWeight (scheduleValue q phase)
            (scheduleValue q (phase + 1)))
          (figureOneFinalScheduledBalancedParameters.proposalCap q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.properStride q
            (scheduleValue q phase))
          (figureOneFinalScheduledBalancedParameters.retryLimit q
            (scheduleValue q phase)) count 0 current) := hcollect.2 0 current
    exact Measure.isProbabilityMeasure_map havg.aemeasurable

/-- Splitting a trace law into live and dead restrictions identifies its
next Gaussian observation law exactly.  Live states run the scaled complete
phase kernel; dead states emit `none` and consume no randomness. -/
theorem bind_scheduledBalancedTracePhaseObservationLaw_eq_live_dead
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (law : Measure (ScheduledBalancedCoolingTrace q.n)) :
    law.bind (scheduledBalancedTracePhaseObservationLaw
        figureOneFinalScheduledBalancedParameters q I phase) =
      (scheduledBalancedTraceLiveStateLaw law
          (fun x => accuracyScaleFactor q • x)).bind
        (figureOneScheduledScaledGaussianPhaseLaw q I phase) +
      (scheduledBalancedTraceDeadStateLaw law
          (fun x => accuracyScaleFactor q • x)) Set.univ •
        Measure.dirac none := by
  let liveSet := scheduledBalancedTraceLiveSet q.n
  let deadSet := scheduledBalancedTraceDeadSet q.n
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let state : ScheduledBalancedCoolingTrace q.n → AmbientSpace q.n :=
    scale ∘ scheduledBalancedTraceRetainedState
  let obs := scheduledBalancedTracePhaseObservationLaw
    figureOneFinalScheduledBalancedParameters q I phase
  let K := figureOneScheduledScaledGaussianPhaseLaw q I phase
  have hobs := scheduledBalancedTracePhaseObservationLaw_measurable_and_probability
    figureOneFinalScheduledBalancedParameters q I phase
  have hK := figureOneScheduledScaledGaussianPhaseLaw_measurable_and_probability
    q I phase
  have hstate : Measurable state := by
    dsimp only [state, scale]
    exact ((measurable_const : Measurable fun _ : AmbientSpace q.n =>
      accuracyScaleFactor q).smul measurable_id).comp
        measurable_scheduledBalancedTraceRetainedState
  have hsplit : law = law.restrict liveSet + law.restrict deadSet := by
    rw [show deadSet = liveSetᶜ by
      exact scheduledBalancedTraceDeadSet_eq_compl,
      Measure.restrict_add_restrict_compl
        measurableSet_scheduledBalancedTraceLiveSet]
  have hlive : (law.restrict liveSet).bind obs =
      ((law.restrict liveSet).map state).bind K := by
    rw [map_bind_eq_bind_comp_state (law.restrict liveSet) hstate hK.1]
    apply Measure.bind_congr_right
    filter_upwards [ae_restrict_mem
      (measurableSet_scheduledBalancedTraceLiveSet (n := q.n))]
      with trace htrace
    rcases trace with ⟨history, live⟩
    cases live with
    | false =>
        simp [liveSet, scheduledBalancedTraceLiveSet] at htrace
    | true =>
        simp only [obs, scheduledBalancedTracePhaseObservationLaw,
          if_true, hphase, K, state, scale, Function.comp_apply,
          scheduledBalancedTraceRetainedState]
        rfl
  have hdead : (law.restrict deadSet).bind obs =
      (law.restrict deadSet) Set.univ • Measure.dirac none := by
    have heq : ∀ᵐ trace ∂(law.restrict deadSet),
        obs trace = Measure.dirac none := by
      filter_upwards [ae_restrict_mem
        (measurableSet_scheduledBalancedTraceDeadSet (n := q.n))]
        with trace htrace
      rcases trace with ⟨history, live⟩
      cases live with
      | false => simp [obs, scheduledBalancedTracePhaseObservationLaw]
      | true => simp [deadSet, scheduledBalancedTraceDeadSet] at htrace
    rw [Measure.bind_congr_right heq, Measure.bind_const]
  calc
    law.bind obs =
        (law.restrict liveSet + law.restrict deadSet).bind obs :=
      congrArg (fun mu => mu.bind obs) hsplit
    _ = (law.restrict liveSet).bind obs +
        (law.restrict deadSet).bind obs :=
      measure_bind_add_left _ _ hobs.1
    _ = ((law.restrict liveSet).map state).bind K +
        (law.restrict deadSet) Set.univ • Measure.dirac none := by
      rw [hlive, hdead]
    _ = _ := by
      congr 2
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter]
      symm
      exact scheduledBalancedTraceDeadStateLaw_apply_univ law scale
        (by fun_prop)

/-- The dead trace mass is bounded by the same optional-retained exact-chance
error: the ideal accepted target is supported on `some`. -/
theorem figureOneScheduledTrace_deadState_mass_le_retainedError
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q)
    (transform : AmbientSpace q.n → AmbientSpace q.n)
    (htransform : Measurable transform) :
    scheduledBalancedTraceDeadStateLaw
        (scheduledBalancedForwardTraceLaw
          figureOneFinalScheduledBalancedParameters q I (phase + 1))
        transform Set.univ ≤
      figureOneScheduledRetainedError q (phase + 1) := by
  let law := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I (phase + 1)
  have hmlu := scheduledBalancedForwardTraceLaw_retained_leUpTo_target
    q I phase hphase
  have hevent := hmlu.event_le ({none} : Set (Option (AmbientSpace q.n)))
  have hnone :
      ((figureOneScheduledAcceptedTargetAt q I phase).map some)
          ({none} : Set (Option (AmbientSpace q.n))) = 0 := by
    rw [Measure.map_apply measurable_some measurableSet_option_none]
    have hemp : some ⁻¹' ({none} : Set (Option (AmbientSpace q.n))) =
        (∅ : Set (AmbientSpace q.n)) := by
      ext point
      simp
    rw [hemp, measure_empty]
  rw [hnone, zero_add] at hevent
  calc
    scheduledBalancedTraceDeadStateLaw law transform Set.univ =
        (law.map scheduledBalancedCoolingTraceProject) {none} :=
      scheduledBalancedTraceDeadStateLaw_mass_eq_project_none
        law transform htransform
    _ = (law.map scheduledBalancedTraceRetainedOption) {none} := by
      rw [Measure.map_apply measurable_scheduledBalancedCoolingTraceProject
          measurableSet_option_none,
        Measure.map_apply measurable_scheduledBalancedTraceRetainedOption
          measurableSet_option_none]
      congr 1
      ext trace
      rcases trace with ⟨history, live⟩
      cases live <;> simp [scheduledBalancedCoolingTraceProject,
        scheduledBalancedTraceRetainedOption]
    _ ≤ figureOneScheduledRetainedError q (phase + 1) := by
      simpa [law] using hevent

/-- The shared retained-error witness split in the form needed by the
live/dead transition lemma: the live marginal is good plus `liveBad`, and
`liveBad` together with the absorbing dead mass costs only the one retained
error budget. -/
theorem exists_figureOneScheduledTraceScaledLive_good_bad
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    let law := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I (phase + 1)
    let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
      accuracyScaleFactor q • x
    let good := (figureOneScheduledAcceptedTargetAt q I phase).map scale
    ∃ liveBad : Measure (AmbientSpace q.n),
      scheduledBalancedTraceLiveStateLaw law scale ≤ good + liveBad ∧
      liveBad Set.univ +
          scheduledBalancedTraceDeadStateLaw law scale Set.univ ≤
        figureOneScheduledRetainedError q (phase + 1) := by
  dsimp only
  let law := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I (phase + 1)
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let good := (figureOneScheduledAcceptedTargetAt q I phase).map scale
  obtain ⟨error, herrorDom, herrorMass⟩ :=
    scheduledBalancedForwardTraceLaw_retained_leUpTo_target
      q I phase hphase
  let someSet := scheduledRetainedSomeSet q.n
  let get := scheduledRetainedGetDZero (n := q.n)
  let liveBad0 := (error.restrict someSet).map get
  let liveBad := liveBad0.map scale
  refine ⟨liveBad, ?_, ?_⟩
  · have hrestrict :
        ((law.map scheduledBalancedTraceRetainedOption).restrict someSet) ≤
          ((((figureOneScheduledAcceptedTargetAt q I phase).map some) +
            error).restrict someSet) :=
      Measure.restrict_mono Set.Subset.rfl herrorDom
    have hmapped := Measure.map_mono hrestrict
      (measurable_scheduledRetainedGetDZero (n := q.n))
    rw [Measure.restrict_add,
      Measure.map_add _ _
        (measurable_scheduledRetainedGetDZero (n := q.n)),
      map_some_restrict_extract_eq] at hmapped
    have hlive0 : scheduledBalancedTraceLiveStateLaw law id ≤
        figureOneScheduledAcceptedTargetAt q I phase + liveBad0 := by
      rw [scheduledBalancedTraceLiveStateLaw_eq_retainedOptionSome]
      exact hmapped
    have hlive := Measure.map_mono hlive0 (by fun_prop : Measurable scale)
    rw [Measure.map_add _ _ (by fun_prop : Measurable scale)] at hlive
    unfold scheduledBalancedTraceLiveStateLaw at hlive ⊢
    rw [Measure.map_map (by fun_prop : Measurable scale)
      ((measurable_id : Measurable fun x : AmbientSpace q.n => x).comp
        (measurable_scheduledBalancedTraceRetainedState (n := q.n)))] at hlive
    simpa [good, liveBad, liveBad0, Function.comp_def] using hlive
  · have hliveBadMass : liveBad Set.univ = error someSet := by
      rw [show liveBad = liveBad0.map scale by rfl,
        Measure.map_apply (by fun_prop : Measurable scale) MeasurableSet.univ,
        Set.preimage_univ]
      rw [show liveBad0 = (error.restrict someSet).map get by rfl,
        Measure.map_apply
          (measurable_scheduledRetainedGetDZero (n := q.n))
          MeasurableSet.univ,
        Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ]
      simp
    have hnone :
        ((figureOneScheduledAcceptedTargetAt q I phase).map some)
            ({none} : Set (Option (AmbientSpace q.n))) = 0 := by
      rw [Measure.map_apply measurable_some measurableSet_option_none]
      have hpreSome : (some : AmbientSpace q.n →
          Option (AmbientSpace q.n)) ⁻¹'
            ({none} : Set (Option (AmbientSpace q.n))) = ∅ := by
        ext point
        simp
      rw [hpreSome, measure_empty]
    have hdeadMass :
        scheduledBalancedTraceDeadStateLaw law scale Set.univ ≤
          error ({none} : Set (Option (AmbientSpace q.n))) := by
      have hevent := Measure.le_iff'.mp herrorDom
        ({none} : Set (Option (AmbientSpace q.n)))
      rw [Measure.add_apply, hnone, zero_add] at hevent
      rw [scheduledBalancedTraceDeadStateLaw_apply_univ law scale
        (by fun_prop : Measurable scale)]
      rw [Measure.map_apply measurable_scheduledBalancedTraceRetainedOption
        measurableSet_option_none] at hevent
      have hpre : scheduledBalancedTraceRetainedOption ⁻¹'
          ({none} : Set (Option (AmbientSpace q.n))) =
            scheduledBalancedTraceDeadSet q.n := by
        ext trace
        rcases trace with ⟨history, live⟩
        cases live <;> simp [scheduledBalancedTraceRetainedOption,
          scheduledBalancedTraceDeadSet]
      simpa [law, hpre] using hevent
    calc
      liveBad Set.univ +
          scheduledBalancedTraceDeadStateLaw law scale Set.univ ≤
        error someSet + error ({none} : Set (Option (AmbientSpace q.n))) := by
          rw [hliveBadMass]
          exact add_le_add le_rfl hdeadMass
      _ = error Set.univ := by
        rw [show someSet =
            ({none} : Set (Option (AmbientSpace q.n)))ᶜ by rfl,
          add_comm,
          measure_add_measure_compl measurableSet_option_none]
      _ ≤ figureOneScheduledRetainedError q (phase + 1) := herrorMass

/-- Fold the absorbing dead-state marginal into the additive bad witness.
The resulting full retained-state law, rather than merely its live
restriction, is dominated by the scaled accepted target plus at most twice
the retained exact-chance error. -/
theorem exists_figureOneScheduledTraceScaledState_good_bad
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ)
    (hphase : phase < terminalPhaseSteps q) :
    let law := scheduledBalancedForwardTraceLaw
      figureOneFinalScheduledBalancedParameters q I (phase + 1)
    let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
      accuracyScaleFactor q • x
    let good := (figureOneScheduledAcceptedTargetAt q I phase).map scale
    ∃ bad : Measure (AmbientSpace q.n),
      scheduledBalancedTraceStateLaw law scale ≤ good + bad ∧
      bad Set.univ ≤ figureOneScheduledRetainedError q (phase + 1) := by
  dsimp only
  let law := scheduledBalancedForwardTraceLaw
    figureOneFinalScheduledBalancedParameters q I (phase + 1)
  let scale : AmbientSpace q.n → AmbientSpace q.n := fun x =>
    accuracyScaleFactor q • x
  let good := (figureOneScheduledAcceptedTargetAt q I phase).map scale
  obtain ⟨error, herrorDom, herrorMass⟩ :=
    scheduledBalancedForwardTraceLaw_retained_leUpTo_target
      q I phase hphase
  let someSet := scheduledRetainedSomeSet q.n
  let get := scheduledRetainedGetDZero (n := q.n)
  let liveBad0 := (error.restrict someSet).map get
  let liveBad := liveBad0.map scale
  let dead := scheduledBalancedTraceDeadStateLaw law scale
  let bad := liveBad + dead
  refine ⟨bad, ?_, ?_⟩
  · rw [scheduledBalancedTraceStateLaw_eq_live_add_dead law scale (by fun_prop)]
    have hlive0 : scheduledBalancedTraceLiveStateLaw law id ≤
        figureOneScheduledAcceptedTargetAt q I phase + liveBad0 := by
      rw [scheduledBalancedTraceLiveStateLaw_eq_retainedOptionSome]
      have hrestrict :
          ((law.map scheduledBalancedTraceRetainedOption).restrict someSet) ≤
            ((((figureOneScheduledAcceptedTargetAt q I phase).map some) +
              error).restrict someSet) :=
        Measure.restrict_mono Set.Subset.rfl herrorDom
      have hmapped := Measure.map_mono hrestrict
        (measurable_scheduledRetainedGetDZero (n := q.n))
      rw [Measure.restrict_add,
        Measure.map_add _ _
          (measurable_scheduledRetainedGetDZero (n := q.n)),
        map_some_restrict_extract_eq] at hmapped
      exact hmapped
    have hlive := Measure.map_mono hlive0 (by fun_prop : Measurable scale)
    rw [Measure.map_add _ _ (by fun_prop : Measurable scale)] at hlive
    unfold scheduledBalancedTraceLiveStateLaw at hlive ⊢
    rw [Measure.map_map (by fun_prop : Measurable scale)
      ((measurable_id : Measurable fun x : AmbientSpace q.n => x).comp
        (measurable_scheduledBalancedTraceRetainedState (n := q.n)))] at hlive
    calc
      scheduledBalancedTraceLiveStateLaw law scale + dead ≤
          (good + liveBad) + dead := by
            gcongr
            change
              (law.restrict (scheduledBalancedTraceLiveSet q.n)).map
                  (scale ∘ scheduledBalancedTraceRetainedState) ≤ _
            simpa [good, liveBad, liveBad0, Function.comp_def] using hlive
      _ = good + bad := by
        simp only [bad]
        ac_rfl
  · rw [show bad = liveBad + dead by rfl, Measure.add_apply]
    have hliveBadMass : liveBad Set.univ = error someSet := by
      rw [show liveBad = liveBad0.map scale by rfl,
        Measure.map_apply (by fun_prop : Measurable scale) MeasurableSet.univ,
        Set.preimage_univ]
      rw [show liveBad0 = (error.restrict someSet).map get by rfl,
        Measure.map_apply
          (measurable_scheduledRetainedGetDZero (n := q.n))
          MeasurableSet.univ,
        Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ]
      simp
    have hnone :
        ((figureOneScheduledAcceptedTargetAt q I phase).map some)
            ({none} : Set (Option (AmbientSpace q.n))) = 0 := by
      rw [Measure.map_apply measurable_some measurableSet_option_none]
      have hpreSome : (some : AmbientSpace q.n →
          Option (AmbientSpace q.n)) ⁻¹'
            ({none} : Set (Option (AmbientSpace q.n))) = ∅ := by
        ext point
        simp
      rw [hpreSome, measure_empty]
    have hdeadMass : dead Set.univ ≤
        error ({none} : Set (Option (AmbientSpace q.n))) := by
      have hevent := Measure.le_iff'.mp herrorDom
        ({none} : Set (Option (AmbientSpace q.n)))
      rw [Measure.add_apply, hnone, zero_add] at hevent
      rw [show dead = scheduledBalancedTraceDeadStateLaw law scale by rfl,
        scheduledBalancedTraceDeadStateLaw_apply_univ law scale
          (by fun_prop : Measurable scale)]
      rw [Measure.map_apply measurable_scheduledBalancedTraceRetainedOption
        measurableSet_option_none] at hevent
      have hpre : scheduledBalancedTraceRetainedOption ⁻¹'
          ({none} : Set (Option (AmbientSpace q.n))) =
            scheduledBalancedTraceDeadSet q.n := by
        ext trace
        rcases trace with ⟨history, live⟩
        cases live <;> simp [scheduledBalancedTraceRetainedOption,
          scheduledBalancedTraceDeadSet]
      simpa [law, hpre] using hevent
    calc
      liveBad Set.univ + dead Set.univ ≤
          error someSet + error ({none} : Set (Option (AmbientSpace q.n))) := by
        rw [hliveBadMass]
        exact add_le_add le_rfl hdeadMass
      _ = error Set.univ := by
        rw [show someSet =
            ({none} : Set (Option (AmbientSpace q.n)))ᶜ by
          rfl,
          add_comm,
          measure_add_measure_compl measurableSet_option_none]
      _ ≤ figureOneScheduledRetainedError q (phase + 1) := herrorMass

#print axioms figureOneScheduledTrace_deadState_mass_le_retainedError
#print axioms exists_figureOneScheduledTraceScaledState_good_bad

end ArlibCommunity.Algorithms.CV18
