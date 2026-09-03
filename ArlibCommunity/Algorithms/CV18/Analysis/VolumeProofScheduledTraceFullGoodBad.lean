/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledGoodBadIndependence
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceDependentAssembly

/-! # Full retained-state good/bad decomposition for the scheduled trace -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Set

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
