/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.ProgramSemantics

/-!
# A single global membership-query cutoff

CV18 bounds the total number of raw ball-walk proposals over the complete
cooling execution.  Applying Markov's inequality separately at every phase
would introduce an unnecessary factor equal to the number of phases.  This
module supplies the operational counterpart of the paper's global cutoff.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory
open scoped ENNReal

/-- Run an oracle program with one shared membership-query budget.  Random
draws do not consume budget.  A pure result at budget zero still succeeds;
only an attempted query past the budget produces `none`. -/
noncomputable def MembershipOracleProgram.withQueryCap
    {n : ℕ} {Result : Type} :
    ℕ → MembershipOracleProgram n Result →
      MembershipOracleProgram n (Option Result)
  | _, .pure result => .pure (some result)
  | 0, .query _ _ => .pure none
  | budget + 1, .query point next =>
      .query point fun answer => withQueryCap budget (next answer)
  | budget, .randomNat law next =>
      .randomNat law fun seed => withQueryCap budget (next seed)
  | budget, .randomPoint law hprob next =>
      .randomPoint law hprob fun point => withQueryCap budget (next point)
  | budget, .randomReal law hprob next =>
      .randomReal law hprob fun value => withQueryCap budget (next value)

/-- The global cap is a genuine worst-case syntax-level query bound. -/
theorem MembershipOracleProgram.withQueryCap_queryBound
    {n : ℕ} {Result : Type} (budget : ℕ)
    (program : MembershipOracleProgram n Result) :
    (program.withQueryCap budget).QueryBound budget := by
  induction program generalizing budget with
  | pure result =>
      exact .pure _ budget
  | query point next ih =>
      cases budget with
      | zero => exact .pure _ 0
      | succ budget =>
          exact .query point _ budget fun answer => ih answer budget
  | randomNat law next ih =>
      exact .randomNat law _ budget fun seed => ih seed budget
  | randomPoint law hprob next ih =>
      exact .randomPoint law hprob _ budget fun point => ih point budget
  | randomReal law hprob next ih =>
      exact .randomReal law hprob _ budget fun value => ih value budget

/-- The result projection performed by the capped interpreter on the exact
result-and-cost semantics. -/
def queryCapOutcome {Result : Type} (budget : ℕ) : Result × ℕ → Option Result :=
  fun outcome => if outcome.2 ≤ budget then some outcome.1 else none

theorem measurable_queryCapOutcome {Result : Type} [MeasurableSpace Result]
    (budget : ℕ) : Measurable (queryCapOutcome (Result := Result) budget) := by
  unfold queryCapOutcome
  exact Measurable.ite
    (measurableSet_le measurable_snd measurable_const)
    (measurable_some.comp measurable_fst) measurable_const

theorem measurableSet_queryCap_none {Result : Type} [MeasurableSpace Result] :
    MeasurableSet ({none} : Set (Option Result)) := by
  let isNone : Option Result → Bool
    | none => true
    | some _ => false
  have hisNone : Measurable isNone := by
    exact Measurable.optionElim true measurable_const
  have heq : ({none} : Set (Option Result)) = isNone ⁻¹' {true} := by
    ext value
    cases value <;> simp [isNone]
  rw [heq]
  exact hisNone (measurableSet_singleton true)

/-- Mapping after a Giry bind can be pushed into the bound kernel.  The
almost-everywhere formulation matches the interpreter's exact measurability
invariant. -/
theorem measure_map_bind_eq_bind_map_ae
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (mu : Measure A) {K : A → Measure B}
    (hK : AEMeasurable K mu) {f : B → C} (hf : Measurable f) :
    (mu.bind K).map f = mu.bind fun x => (K x).map f := by
  ext S hS
  rw [Measure.map_apply hf hS, Measure.bind_apply (hf hS) hK]
  have hmap : AEMeasurable (fun x => (K x).map f) mu :=
    (Measure.measurable_map f hf).comp_aemeasurable hK
  rw [Measure.bind_apply hS hmap]
  apply lintegral_congr_ae
  filter_upwards with x
  rw [Measure.map_apply hf hS]

/-- Exact semantics of the global cutoff: execute the original program with
its interpreter-counted cost, retain its result iff that cost is within the
budget, and otherwise return `none`. -/
theorem MembershipOracleProgram.runEstimate_withQueryCap
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool) :
    ∀ (program : MembershipOracleProgram n Result) (budget : ℕ),
      program.ExecutionMeasurable oracle →
      (program.withQueryCap budget).runEstimate oracle =
        (program.run oracle).map (queryCapOutcome budget) := by
  intro program
  induction program with
  | pure result =>
      intro budget _
      simp only [MembershipOracleProgram.withQueryCap,
        MembershipOracleProgram.runEstimate, MembershipOracleProgram.run]
      rw [Measure.map_dirac' (measurable_queryCapOutcome budget)]
      simp [queryCapOutcome]
  | query point next ih =>
      intro budget hmeas
      change (next (oracle point)).ExecutionMeasurable oracle at hmeas
      cases budget with
      | zero =>
          simp only [MembershipOracleProgram.withQueryCap,
            MembershipOracleProgram.runEstimate, MembershipOracleProgram.run]
          rw [Measure.map_map (measurable_queryCapOutcome 0) (by fun_prop)]
          have hfun : queryCapOutcome (Result := Result) 0 ∘
              (fun outcome : Result × ℕ => (outcome.1, outcome.2 + 1)) =
              fun _ => none := by
            funext outcome
            simp [queryCapOutcome]
          rw [hfun, Measure.map_const]
          let _ : IsProbabilityMeasure
              ((next (oracle point)).run oracle) :=
            MembershipOracleProgram.run_isProbabilityMeasure oracle _ hmeas
          simp
      | succ budget =>
          simp only [MembershipOracleProgram.withQueryCap,
            MembershipOracleProgram.runEstimate, MembershipOracleProgram.run]
          rw [ih (oracle point) budget hmeas,
            Measure.map_map (measurable_queryCapOutcome (budget + 1)) (by fun_prop)]
          congr 1
          funext outcome
          simp [queryCapOutcome]
  | randomNat law next ih =>
      intro budget hmeas
      simp only [MembershipOracleProgram.ExecutionMeasurable] at hmeas
      simp only [MembershipOracleProgram.withQueryCap,
        MembershipOracleProgram.runEstimate, MembershipOracleProgram.run]
      rw [measure_map_bind_eq_bind_map_ae law.toMeasure hmeas.1
        (measurable_queryCapOutcome budget)]
      apply Measure.bind_congr_right
      filter_upwards [hmeas.2] with seed hseed
      exact ih seed budget hseed
  | randomPoint law hprob next ih =>
      intro budget hmeas
      simp only [MembershipOracleProgram.ExecutionMeasurable] at hmeas
      simp only [MembershipOracleProgram.withQueryCap,
        MembershipOracleProgram.runEstimate, MembershipOracleProgram.run]
      rw [measure_map_bind_eq_bind_map_ae law hmeas.1
        (measurable_queryCapOutcome budget)]
      apply Measure.bind_congr_right
      filter_upwards [hmeas.2] with point hpoint
      exact ih point budget hpoint
  | randomReal law hprob next ih =>
      intro budget hmeas
      simp only [MembershipOracleProgram.ExecutionMeasurable] at hmeas
      simp only [MembershipOracleProgram.withQueryCap,
        MembershipOracleProgram.runEstimate, MembershipOracleProgram.run]
      rw [measure_map_bind_eq_bind_map_ae law hmeas.1
        (measurable_queryCapOutcome budget)]
      apply Measure.bind_congr_right
      filter_upwards [hmeas.2] with value hvalue
      exact ih value budget hvalue

/-- Failure of the capped program is exactly the event that the original
execution traverses more query nodes than the shared budget. -/
theorem MembershipOracleProgram.runEstimate_withQueryCap_apply_none
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n Result) (budget : ℕ)
    (hmeas : program.ExecutionMeasurable oracle) :
    (program.withQueryCap budget).runEstimate oracle {none} =
      program.run oracle {outcome | budget < outcome.2} := by
  rw [program.runEstimate_withQueryCap oracle budget hmeas,
    Measure.map_apply (measurable_queryCapOutcome budget)
      measurableSet_queryCap_none]
  congr 1
  ext outcome
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  simp [queryCapOutcome]

/-- A direct Markov bound for exhausting the one global cutoff. -/
theorem MembershipOracleProgram.mul_runEstimate_withQueryCap_none_le_cost
    {n : ℕ} {Result : Type} [MeasurableSpace Result]
    (oracle : AmbientSpace n → Bool)
    (program : MembershipOracleProgram n Result) (budget : ℕ)
    (hmeas : program.ExecutionMeasurable oracle) :
    (budget + 1 : ℝ≥0∞) *
        (program.withQueryCap budget).runEstimate oracle {none} ≤
      ∫⁻ outcome, (outcome.2 : ℝ≥0∞) ∂(program.run oracle) := by
  rw [program.runEstimate_withQueryCap_apply_none oracle budget hmeas]
  have hmarkov := mul_meas_ge_le_lintegral
    (show Measurable fun outcome : Result × ℕ => (outcome.2 : ℝ≥0∞) by fun_prop)
    (budget + 1 : ℝ≥0∞) (μ := program.run oracle)
  simpa only [Nat.cast_add, Nat.cast_one,
    show ({outcome : Result × ℕ | budget < outcome.2} =
      {outcome : Result × ℕ |
        (budget + 1 : ℝ≥0∞) ≤ (outcome.2 : ℝ≥0∞)}) by
      ext outcome
      simp only [Set.mem_ofPred_eq]
      exact_mod_cast Nat.add_one_le_iff] using hmarkov

end ArlibCommunity.Algorithms.CV18
