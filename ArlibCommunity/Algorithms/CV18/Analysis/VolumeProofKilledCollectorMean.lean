/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCollectorEndpoint
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBoundedObservableAETransfer

/-!
# Marginal means of a killed retained collector

The executable phase collector discards its accumulated total if a later
retry fails.  For first-moment comparisons it is useful to retain that total
in a shadow state and kill it only in the final observation.  This module
constructs that shadow without changing the retained optional-state chain.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A weight on a retained optional state, with a dead state contributing
zero. -/
def retainedOptionWeight (weight : S → ℝ) : Option S → ℝ
  | none => 0
  | some state => weight state

theorem measurable_retainedOptionWeight {S : Type*} [MeasurableSpace S]
    {weight : S → ℝ} (hweight : Measurable weight) :
    Measurable (retainedOptionWeight weight) := by
  unfold retainedOptionWeight
  convert Measurable.optionElim (0 : ℝ) hweight using 1
  funext state
  cases state <;> rfl

/-- Shadow one-step kernel.  Unlike the public optional collector, a killed
state retains the total accumulated before death. -/
noncomputable def retainedSumKernel
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (weight : S → ℝ) :
    (ℝ × Option S) → Measure (ℝ × Option S) := fun state =>
  (K state.2).map fun next =>
    (state.1 + retainedOptionWeight weight next, next)

theorem retainedSumKernel_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight) :
    Measurable (retainedSumKernel K weight) ∧
      ∀ state, IsProbabilityMeasure (retainedSumKernel K weight state) := by
  have hwopt : Measurable (retainedOptionWeight weight) :=
    measurable_retainedOptionWeight hweight
  have hout : Measurable fun value : (ℝ × Option S) × Option S =>
      (value.1.1 + retainedOptionWeight weight value.2, value.2) :=
    ((measurable_fst.comp measurable_fst).add
      (hwopt.comp measurable_snd)).prodMk measurable_snd
  constructor
  · unfold retainedSumKernel
    apply measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun state => hKprob state.2)
    convert hout using 1
  · intro state
    unfold retainedSumKernel
    let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
    exact Measure.isProbabilityMeasure_map
      ((measurable_const.add hwopt).prodMk measurable_id).aemeasurable

/-- Forget the shadow total. -/
def retainedSumState {S : Type*} : ℝ × Option S → Option S := Prod.snd

/-- Expose the accumulated total only if the retained chain is still live. -/
def retainedLiveTotal {S : Type*} : ℝ × Option S → ℝ
  | (_total, none) => 0
  | (total, some _) => total

/-- Convert a shadow state back to the public optional collector output. -/
def retainedSumOutput {S : Type*} : ℝ × Option S → Option (ℝ × S)
  | (_, none) => none
  | (total, some state) => some (total, state)

theorem measurable_retainedLiveTotal {S : Type*} [MeasurableSpace S] :
    Measurable (retainedLiveTotal (S := S)) := by
  let noneValue : ℝ → ℝ := fun _ => 0
  let someValue : ℝ × S → ℝ := fun value => value.1
  have hnone : Measurable noneValue := measurable_const
  have hsome : Measurable someValue := measurable_fst
  convert Measurable.optionElimParam hnone hsome using 1
  funext state
  rcases state with ⟨_total, state⟩
  cases state <;> rfl

theorem measurable_retainedSumOutput {S : Type*} [MeasurableSpace S] :
    Measurable (retainedSumOutput (S := S)) := by
  let noneValue : ℝ → Option (ℝ × S) := fun _ => none
  let someValue : ℝ × S → Option (ℝ × S) := fun value => some value
  have hnone : Measurable noneValue := measurable_const
  have hsome : Measurable someValue := measurable_some
  convert Measurable.optionElimParam hnone hsome using 1
  funext state
  rcases state with ⟨total, state⟩
  cases state <;> rfl

@[simp] theorem scheduledBalancedPhaseRatio_retainedSumOutput
    {S : Type*} (state : ℝ × Option S) :
    (match retainedSumOutput state with
      | none => 0
      | some result => result.1) = retainedLiveTotal state := by
  rcases state with ⟨total, state⟩
  cases state <;> rfl

/-- The shadow construction does not alter the optional retained-state
chain at any finite horizon. -/
theorem map_iterated_retainedSumKernel_state
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (hK : Measurable K)
    (hKprob : ∀ state, IsProbabilityMeasure (K state))
    (weight : S → ℝ) (hweight : Measurable weight)
    (initial : Measure (ℝ × Option S)) : ∀ steps,
    (iteratedKernelLaw (fun _ => retainedSumKernel K weight)
      initial steps).map retainedSumState =
    iteratedKernelLaw (fun _ => K)
      (initial.map retainedSumState) steps := by
  have hsum := retainedSumKernel_measurable_and_probability
    K hK hKprob weight hweight
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iteratedKernelLaw_succ, iteratedKernelLaw_succ]
      let old := iteratedKernelLaw
        (fun _ => retainedSumKernel K weight) initial steps
      have hpoint : (fun state : ℝ × Option S =>
          (retainedSumKernel K weight state).map retainedSumState) =
          K ∘ retainedSumState := by
        funext state
        unfold retainedSumKernel retainedSumState
        have hout : Measurable fun next : Option S =>
            (state.1 + retainedOptionWeight weight next, next) :=
          (measurable_const.add
            (measurable_retainedOptionWeight hweight)).prodMk measurable_id
        simpa [Function.comp_def] using
          (Measure.map_map (μ := K state.2) measurable_snd hout)
      calc
        (old.bind (retainedSumKernel K weight)).map retainedSumState =
            old.bind fun state =>
              (retainedSumKernel K weight state).map retainedSumState :=
          map_bind_eq_bind_map_of_measurable old hsum.1 measurable_snd
        _ = old.bind (K ∘ retainedSumState) := by rw [hpoint]
        _ = (old.map retainedSumState).bind K :=
          (map_bind_eq_bind_comp_state old measurable_snd hK).symm
        _ = (iteratedKernelLaw (fun _ => K)
            (initial.map retainedSumState) steps).bind K := by rw [ih]

/-- Pointwise, one shadow step increments the total by exactly the weight of
the new retained state (zero after death). -/
theorem retainedSumKernel_total_eq
    {S : Type*} [MeasurableSpace S]
    (K : Option S → Measure (Option S)) (weight : S → ℝ)
    (hweight : Measurable weight)
    (state : ℝ × Option S) :
    (retainedSumKernel K weight state).map Prod.fst =
      (K state.2).map
        (fun next => state.1 + retainedOptionWeight weight next) := by
  unfold retainedSumKernel
  have hout : Measurable fun next : Option S =>
      (state.1 + retainedOptionWeight weight next, next) :=
    (measurable_const.add
      (measurable_retainedOptionWeight hweight)).prodMk measurable_id
  simpa [Function.comp_def] using
    (Measure.map_map (μ := K state.2) measurable_fst hout)

/-! ## Loss from killing the accumulated sum -/

/-- Killing the shadow total only on dead outcomes loses at most the
deterministic total bound times the final death probability. -/
theorem integral_retainedLiveTotal_loss_le
    {S : Type*} [MeasurableSpace S]
    (mu : Measure (ℝ × Option S)) [IsProbabilityMeasure mu]
    {C : ℝ} (hC : 0 ≤ C)
    (htotal0 : ∀ᵐ state ∂mu, 0 ≤ state.1)
    (htotalC : ∀ᵐ state ∂mu, state.1 ≤ C) :
    0 ≤ (∫ state, state.1 ∂mu) -
        ∫ state, retainedLiveTotal state ∂mu ∧
      (∫ state, state.1 ∂mu) -
          ∫ state, retainedLiveTotal state ∂mu ≤
        C * mu.real {state | state.2 = none} := by
  let dead : Set (ℝ × Option S) := {state | state.2 = none}
  have hdead : MeasurableSet dead :=
    measurable_snd measurableSet_option_none
  have hfstInt : Integrable (fun state : ℝ × Option S => state.1) mu := by
    apply Integrable.of_bound measurable_fst.aestronglyMeasurable C
    filter_upwards [htotal0, htotalC] with state hstate0 hstateC
    simpa [Real.norm_eq_abs, abs_of_nonneg hstate0] using hstateC
  have hlive0 : ∀ᵐ state ∂mu, 0 ≤ retainedLiveTotal state := by
    filter_upwards [htotal0] with state hstate0
    rcases state with ⟨total, state⟩
    cases state <;> simp [retainedLiveTotal, hstate0]
  have hliveC : ∀ᵐ state ∂mu, retainedLiveTotal state ≤ C := by
    filter_upwards [htotalC] with state hstateC
    rcases state with ⟨total, state⟩
    cases state <;> simp [retainedLiveTotal, hC, hstateC]
  have hliveInt : Integrable (retainedLiveTotal (S := S)) mu := by
    apply Integrable.of_bound
      measurable_retainedLiveTotal.aestronglyMeasurable C
    filter_upwards [hlive0, hliveC] with state hstate0 hstateC
    simpa [Real.norm_eq_abs, abs_of_nonneg hstate0] using hstateC
  have hindInt : Integrable (dead.indicator (fun _ => C)) mu := by
    apply Integrable.of_bound
      (measurable_const.indicator hdead).aestronglyMeasurable C
    filter_upwards with state
    by_cases hstate : state ∈ dead
    · simp [Set.indicator_of_mem hstate, Real.norm_eq_abs, abs_of_nonneg hC]
    · simpa [Set.indicator, hstate] using hC
  have hliveLe : ∫ state, retainedLiveTotal state ∂mu ≤
      ∫ state, state.1 ∂mu :=
    integral_mono_ae hliveInt hfstInt <| by
      filter_upwards [htotal0] with state hstate0
      rcases state with ⟨total, state⟩
      cases state <;> simp [retainedLiveTotal, hstate0]
  constructor
  · linarith
  · rw [← integral_sub hfstInt hliveInt]
    calc
      (∫ state, state.1 - retainedLiveTotal state ∂mu) ≤
          ∫ state, dead.indicator (fun _ => C) state ∂mu := by
        apply integral_mono_ae (hfstInt.sub hliveInt) hindInt
        filter_upwards [htotal0, htotalC] with state hstate0 hstateC
        rcases state with ⟨total, state⟩
        cases state with
        | none => simpa [dead, retainedLiveTotal] using hstateC
        | some value => simp [dead, retainedLiveTotal]
      _ = mu.real dead * C := integral_indicator_const C hdead
      _ = C * mu.real {state | state.2 = none} := by
        rw [mul_comm]

#print axioms retainedSumKernel_measurable_and_probability
#print axioms map_iterated_retainedSumKernel_state
#print axioms integral_retainedLiveTotal_loss_le

end ArlibCommunity.Algorithms.CV18
