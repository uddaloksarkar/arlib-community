/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.SequentialRecordedKernelPreservation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledChronologicalResetReference

/-!
# Joint preservation of completed chronological coordinates

A coordinatewise list of marginal identities is enough to retain moments but
not enough to retain earlier approximate-independence statements.  This file
packages all completed scalar coordinates as one finite measurable prefix.
A valid trace append preserves that prefix pointwise, hence a
history-preserving reset preserves its complete joint law.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable section

/-- A history-preserving reset followed by a valid trace append preserves the
complete joint law of all already completed coordinates. -/
theorem map_scheduledResetPrefixCoordinates_resetAppend_eq
    (q : VolumeParams) (phase : ℕ)
    (hphase : phase < figureOneDependentPhaseCount q)
    (reset : Measure (ScheduledBalancedCoolingTrace q.n ×
      (ℝ × Option (AmbientSpace q.n))))
    (source : Measure (ScheduledBalancedCoolingTrace q.n))
    (hfst : reset.map Prod.fst = source)
    (hvalid : ∀ᵐ trace ∂source,
      ScheduledBalancedCoolingTraceValid phase trace) :
    (reset.map (scheduledResetTraceAppend (n := q.n))).map
        (scheduledResetPrefixCoordinates q phase) =
      source.map (scheduledResetPrefixCoordinates q phase) := by
  apply map_map_uncurry_update_eq_source_of_ae reset source
    (fun trace result => scheduledResetTraceAppend (trace, result))
    (scheduledResetPrefixCoordinates q phase)
    measurable_scheduledResetTraceAppend
    (measurable_scheduledResetPrefixCoordinates q phase) hfst
  have hvalidReset : ∀ᵐ state ∂reset,
      ScheduledBalancedCoolingTraceValid phase state.1 := by
    have hmapped : ∀ᵐ trace ∂reset.map Prod.fst,
        ScheduledBalancedCoolingTraceValid phase trace := by
      rw [hfst]
      exact hvalid
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_scheduledBalancedCoolingTraceValid phase)).1 hmapped
  filter_upwards [hvalidReset] with state hstate
  exact scheduledResetPrefixCoordinates_resetAppend_eq
    q phase hphase state.1 hstate state.2

/-- Any measurable scalar observable of an exactly preserved prefix retains
its `L²` membership, mean, and second moment. -/
theorem coordinate_moments_of_shared_prefix_law
    {H H' P : Type*} [MeasurableSpace H] [MeasurableSpace H']
    [MeasurableSpace P]
    (source : Measure H) (reference : Measure H')
    (oldMap : H → P) (newMap : H' → P) (F : P → ℝ)
    (hOldMap : Measurable oldMap) (hNewMap : Measurable newMap)
    (hF : Measurable F)
    (hlaw : reference.map newMap = source.map oldMap)
    (hmem : MemLp (F ∘ oldMap) 2 source) :
    MemLp (F ∘ newMap) 2 reference ∧
      (∫ state, F (newMap state) ∂reference) =
        ∫ state, F (oldMap state) ∂source ∧
      (∫ state, F (newMap state) ^ 2 ∂reference) =
        ∫ state, F (oldMap state) ^ 2 ∂source := by
  apply coordinate_moments_of_map_eq source reference
    (F ∘ oldMap) (F ∘ newMap) (hF.comp hOldMap) (hF.comp hNewMap)
  · calc
      reference.map (F ∘ newMap) =
          (reference.map newMap).map F :=
        (Measure.map_map hF hNewMap).symm
      _ = (source.map oldMap).map F := by rw [hlaw]
      _ = source.map (F ∘ oldMap) := Measure.map_map hF hOldMap
  · exact hmem

/-- Approximate independence of two measurable functions of a prefix depends
only on the prefix's joint law.  Thus all prior Lemma 7.17(c) facts transport
unchanged once the complete prefix pushforward is preserved. -/
theorem ApproxIndepFun.of_shared_prefix_law
    {H H' P S T : Type*} [MeasurableSpace H] [MeasurableSpace H']
    [MeasurableSpace P] [MeasurableSpace S] [MeasurableSpace T]
    (source : Measure H) (reference : Measure H')
    (oldMap : H → P) (newMap : H' → P)
    (F : P → S) (G : P → T)
    (hOldMap : Measurable oldMap) (hNewMap : Measurable newMap)
    (hF : Measurable F) (hG : Measurable G)
    (hlaw : reference.map newMap = source.map oldMap)
    {epsilon : ℝ}
    (hind : ApproxIndepFun epsilon (F ∘ oldMap) (G ∘ oldMap) source) :
    ApproxIndepFun epsilon (F ∘ newMap) (G ∘ newMap) reference := by
  apply ApproxIndepFun.of_map_pair_eq
    (hF.comp hOldMap) (hG.comp hOldMap)
    (hF.comp hNewMap) (hG.comp hNewMap) _ hind
  let pair : P → S × T := fun values => (F values, G values)
  have hpair : Measurable pair := hF.prodMk hG
  calc
    source.map (fun state => (F (oldMap state), G (oldMap state))) =
        (source.map oldMap).map pair :=
      (Measure.map_map hpair hOldMap).symm
    _ = (reference.map newMap).map pair := by rw [hlaw]
    _ = reference.map
        (fun state => (F (newMap state), G (newMap state))) :=
      Measure.map_map hpair hNewMap

#print axioms map_scheduledResetPrefixCoordinates_resetAppend_eq
#print axioms coordinate_moments_of_shared_prefix_law
#print axioms ApproxIndepFun.of_shared_prefix_law

end

end ArlibCommunity.Algorithms.CV18
