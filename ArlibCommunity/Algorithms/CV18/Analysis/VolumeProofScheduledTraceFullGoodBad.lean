/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTraceRetainedInduction

/-! # Full retained-state good/bad decomposition for the scheduled trace -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Set

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
