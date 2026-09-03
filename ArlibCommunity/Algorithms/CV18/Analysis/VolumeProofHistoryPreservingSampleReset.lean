/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExactChance

/-!
# History-preserving reset before recording a sample

The finite-walk replacement in CV18 must not first append a score and then
try to replace its source sample.  The correct order is:

1. run the operational next-state kernel;
2. reset only the new-state marginal, preserving the old recorded history;
3. append the observable of the reset state.

This file isolates the measure-theoretic bookkeeping for that order.  The
actual reset construction is deliberately an input: a coupling theorem may
produce it from a TV estimate on the new-state marginal.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Run one operational transition but do not yet record its observable. -/
noncomputable def historyRawNextKernel
    {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (K : X → Measure X) : H × X → Measure (H × X) :=
  fun state => (K state.2).map (Prod.mk state.1)

theorem historyRawNextKernel_measurable_and_probability
    {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (K : X → Measure X) (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x)) :
    Measurable (historyRawNextKernel (H := H) K) ∧
      ∀ state, IsProbabilityMeasure (historyRawNextKernel (H := H) K state) := by
  have hpair : Measurable fun value : (H × X) × X =>
      (value.1.1, value.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  constructor
  · unfold historyRawNextKernel
    exact measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun state => hKprob state.2) hpair
  · intro state
    unfold historyRawNextKernel
    let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
    exact Measure.isProbabilityMeasure_map
      (measurable_const.prodMk measurable_id).aemeasurable

/-- Append the observable of a reset state, retaining that reset state as the
operational state for the following step. -/
def historyRecordResetState
    {H X Y : Type*}
    (record : H → Y → H) (observe : X → Y) : H × X → H × X :=
  fun state => (record state.1 (observe state.2), state.2)

theorem measurable_historyRecordResetState
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (record : H → Y → H) (observe : X → Y)
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) :
    Measurable (historyRecordResetState record observe) := by
  exact (hrecord.comp
      (measurable_fst.prodMk (hobserve.comp measurable_snd))).prodMk
    measurable_snd

/-- The executable one-step kernel, written directly as transition followed
by recording. -/
noncomputable def historyOperationalRecordKernel
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y) :
    H × X → Measure (H × X) :=
  fun state => (K state.2).map fun next =>
    (record state.1 (observe next), next)

theorem historyOperationalRecordKernel_measurable_and_probability
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) :
    Measurable (historyOperationalRecordKernel K record observe) ∧
      ∀ state, IsProbabilityMeasure
        (historyOperationalRecordKernel K record observe state) := by
  have hupdate : Measurable fun value : (H × X) × X =>
      (record value.1.1 (observe value.2), value.2) :=
    (hrecord.comp ((measurable_fst.comp measurable_fst).prodMk
      (hobserve.comp measurable_snd))).prodMk measurable_snd
  constructor
  · unfold historyOperationalRecordKernel
    exact measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun state => hKprob state.2) hupdate
  · intro state
    unfold historyOperationalRecordKernel
    let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
    exact Measure.isProbabilityMeasure_map
      (hupdate.comp (measurable_const.prodMk measurable_id)).aemeasurable

/-- Running the operational transition and then recording is exactly the
direct executable recording kernel. -/
theorem bind_historyRawNextKernel_map_record_eq
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (prefixLaw : Measure (H × X))
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) :
    (prefixLaw.bind (historyRawNextKernel K)).map
        (historyRecordResetState record observe) =
      prefixLaw.bind (historyOperationalRecordKernel K record observe) := by
  have hraw := historyRawNextKernel_measurable_and_probability
    (H := H) K hK hKprob
  have hrecordState := measurable_historyRecordResetState
    record observe hrecord hobserve
  rw [map_bind_eq_bind_map_of_measurable prefixLaw hraw.1 hrecordState]
  apply Measure.bind_congr_right
  filter_upwards with state
  unfold historyRawNextKernel historyOperationalRecordKernel
  calc
    ((K state.2).map (Prod.mk state.1)).map
          (historyRecordResetState record observe) =
        (K state.2).map
          (historyRecordResetState record observe ∘ Prod.mk state.1) :=
      Measure.map_map hrecordState
        (measurable_const.prodMk measurable_id)
    _ = (K state.2).map (fun next =>
        (record state.1 (observe next), next)) := by rfl

/-- A history-preserving reset of the raw next-state law can be pushed
through recording without increasing its additive comparison error. -/
theorem MeasureLeUpTo.historyOperationalRecord_of_rawReset
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (prefixLaw reset : Measure (H × X))
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) {epsilon : ENNReal}
    (hreset : MeasureLeUpTo
      (prefixLaw.bind (historyRawNextKernel K)) reset epsilon) :
    MeasureLeUpTo
      (prefixLaw.bind (historyOperationalRecordKernel K record observe))
      (reset.map (historyRecordResetState record observe)) epsilon := by
  rw [← bind_historyRawNextKernel_map_record_eq prefixLaw K record observe
    hK hKprob hrecord hobserve]
  exact hreset.map
    (measurable_historyRecordResetState record observe hrecord hobserve)

/-- If `readNew` reads the freshly appended coordinate, the reference law
obtained by reset-before-recording gives that coordinate exactly the target
observable marginal. -/
theorem map_recorded_newCoordinate_eq_of_reset_marginal
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (reset : Measure (H × X)) (target : Measure X)
    (record : H → Y → H) (observe : X → Y) (readNew : H → Y)
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) (hreadNew : Measurable readNew)
    (hreadRecord : ∀ history x,
      readNew (record history (observe x)) = observe x)
    (hmarginal : reset.map Prod.snd = target) :
    (reset.map (historyRecordResetState record observe)).map
        (readNew ∘ Prod.fst) = target.map observe := by
  have hrecordState := measurable_historyRecordResetState
    record observe hrecord hobserve
  rw [Measure.map_map (hreadNew.comp measurable_fst) hrecordState]
  have heq : (readNew ∘ Prod.fst) ∘
      historyRecordResetState record observe = observe ∘ Prod.snd := by
    funext state
    exact hreadRecord state.1 state.2
  rw [heq, ← Measure.map_map hobserve measurable_snd, hmarginal]

/-! ## Shadow reset that preserves the operational state

For the executable collector the reset sample is only a shadow used for the
recorded score.  The actual next state must remain available for the next
walk block.  We therefore duplicate the raw next state, preserve the first
copy together with the history, and reset only the second copy.
-/

/-- Run the operational transition and retain both an operational and a
shadow copy of the raw next state. -/
noncomputable def historyRawNextWithCopyKernel
    {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (K : X → Measure X) : H × X → Measure ((H × X) × X) :=
  fun state => (K state.2).map fun next => ((state.1, next), next)

theorem historyRawNextWithCopyKernel_measurable_and_probability
    {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    (K : X → Measure X) (hK : Measurable K)
    (hKprob : ∀ x, IsProbabilityMeasure (K x)) :
    Measurable (historyRawNextWithCopyKernel (H := H) K) ∧
      ∀ state, IsProbabilityMeasure
        (historyRawNextWithCopyKernel (H := H) K state) := by
  have hcopy : Measurable fun value : (H × X) × X =>
      ((value.1.1, value.2), value.2) :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      measurable_snd
  constructor
  · unfold historyRawNextWithCopyKernel
    exact measurable_measure_map_param_variable
      (hK.comp measurable_snd) (fun state => hKprob state.2) hcopy
  · intro state
    unfold historyRawNextWithCopyKernel
    let _ : IsProbabilityMeasure (K state.2) := hKprob state.2
    exact Measure.isProbabilityMeasure_map
      (((measurable_const.prodMk measurable_id).prodMk
        measurable_id)).aemeasurable

/-- Record the observable of the reset shadow, while carrying the untouched
operational copy into the next executable step. -/
def historyRecordShadowState
    {H X Y : Type*}
    (record : H → Y → H) (observe : X → Y) : ((H × X) × X) → H × X :=
  fun state => (record state.1.1 (observe state.2), state.1.2)

theorem measurable_historyRecordShadowState
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (record : H → Y → H) (observe : X → Y)
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) :
    Measurable (historyRecordShadowState record observe) := by
  exact (hrecord.comp
      ((measurable_fst.comp measurable_fst).prodMk
        (hobserve.comp measurable_snd))).prodMk
    (measurable_snd.comp measurable_fst)

/-- Before reset the two copies coincide, so recording the shadow copy is
exactly the executable transition-and-record kernel. -/
theorem bind_historyRawNextWithCopy_map_recordShadow_eq
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (prefixLaw : Measure (H × X))
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) :
    (prefixLaw.bind (historyRawNextWithCopyKernel K)).map
        (historyRecordShadowState record observe) =
      prefixLaw.bind (historyOperationalRecordKernel K record observe) := by
  have hraw := historyRawNextWithCopyKernel_measurable_and_probability
    (H := H) K hK hKprob
  have hrecordShadow := measurable_historyRecordShadowState
    record observe hrecord hobserve
  rw [map_bind_eq_bind_map_of_measurable prefixLaw hraw.1 hrecordShadow]
  apply Measure.bind_congr_right
  filter_upwards with state
  unfold historyRawNextWithCopyKernel historyOperationalRecordKernel
  calc
    ((K state.2).map (fun next => ((state.1, next), next))).map
          (historyRecordShadowState record observe) =
        (K state.2).map
          (historyRecordShadowState record observe ∘
            fun next => ((state.1, next), next)) :=
      Measure.map_map hrecordShadow
        ((measurable_const.prodMk measurable_id).prodMk measurable_id)
    _ = (K state.2).map (fun next =>
        (record state.1 (observe next), next)) := by rfl

/-- The paper-faithful one-sample replacement: reset only the shadow copy,
then record its score.  The operational next state is untouched. -/
theorem MeasureLeUpTo.historyOperationalRecord_of_shadowReset
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (prefixLaw : Measure (H × X)) (reset : Measure ((H × X) × X))
    (K : X → Measure X) (record : H → Y → H) (observe : X → Y)
    (hK : Measurable K) (hKprob : ∀ x, IsProbabilityMeasure (K x))
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) {epsilon : ENNReal}
    (hreset : MeasureLeUpTo
      (prefixLaw.bind (historyRawNextWithCopyKernel K)) reset epsilon) :
    MeasureLeUpTo
      (prefixLaw.bind (historyOperationalRecordKernel K record observe))
      (reset.map (historyRecordShadowState record observe)) epsilon := by
  rw [← bind_historyRawNextWithCopy_map_recordShadow_eq
    prefixLaw K record observe hK hKprob hrecord hobserve]
  exact hreset.map
    (measurable_historyRecordShadowState record observe hrecord hobserve)

/-- An exact reset shadow gives the freshly recorded score exactly the
target observable marginal. -/
theorem map_shadowRecorded_newCoordinate_eq_of_reset_marginal
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (reset : Measure ((H × X) × X)) (target : Measure X)
    (record : H → Y → H) (observe : X → Y) (readNew : H → Y)
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe) (hreadNew : Measurable readNew)
    (hreadRecord : ∀ history x,
      readNew (record history (observe x)) = observe x)
    (hmarginal : reset.map Prod.snd = target) :
    (reset.map (historyRecordShadowState record observe)).map
        (readNew ∘ Prod.fst) = target.map observe := by
  have hrecordShadow := measurable_historyRecordShadowState
    record observe hrecord hobserve
  rw [Measure.map_map (hreadNew.comp measurable_fst) hrecordShadow]
  have heq : (readNew ∘ Prod.fst) ∘
      historyRecordShadowState record observe = observe ∘ Prod.snd := by
    funext state
    exact hreadRecord state.1.1 state.2
  rw [heq, ← Measure.map_map hobserve measurable_snd, hmarginal]

/-- Preserving the raw `(history, operationalNext)` coordinate in the reset
preserves the next operational-state marginal after the shadow score is
recorded. -/
theorem map_shadowRecorded_operationalState_eq_of_reset_history
    {H X Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Y]
    (raw reset : Measure ((H × X) × X))
    (record : H → Y → H) (observe : X → Y)
    (hrecord : Measurable (Function.uncurry record))
    (hobserve : Measurable observe)
    (hhistory : reset.map Prod.fst = raw.map Prod.fst) :
    (reset.map (historyRecordShadowState record observe)).map Prod.snd =
      (raw.map (historyRecordShadowState record observe)).map Prod.snd := by
  have hrecordShadow := measurable_historyRecordShadowState
    record observe hrecord hobserve
  rw [Measure.map_map measurable_snd hrecordShadow,
    Measure.map_map measurable_snd hrecordShadow]
  have heq : Prod.snd ∘ historyRecordShadowState record observe =
      Prod.snd ∘ Prod.fst := by rfl
  rw [heq, ← Measure.map_map measurable_snd measurable_fst,
    ← Measure.map_map measurable_snd measurable_fst, hhistory]

#print axioms historyRawNextKernel_measurable_and_probability
#print axioms historyOperationalRecordKernel_measurable_and_probability
#print axioms bind_historyRawNextKernel_map_record_eq
#print axioms MeasureLeUpTo.historyOperationalRecord_of_rawReset
#print axioms map_recorded_newCoordinate_eq_of_reset_marginal
#print axioms historyRawNextWithCopyKernel_measurable_and_probability
#print axioms bind_historyRawNextWithCopy_map_recordShadow_eq
#print axioms MeasureLeUpTo.historyOperationalRecord_of_shadowReset
#print axioms map_shadowRecorded_newCoordinate_eq_of_reset_marginal
#print axioms map_shadowRecorded_operationalState_eq_of_reset_history

end

end ArlibCommunity.Algorithms.CV18
