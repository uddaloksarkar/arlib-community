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

/-! ## Concrete factorization of the Lemma 7.17(c) observables -/

/-- Total one-based coordinate reader on a finite reset prefix.  Only the
used interval matters; zero is a harmless value outside it. -/
noncomputable def scheduledResetPrefixPhaseVariable
    (phase j : ℕ) (values : Fin phase → ℝ) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ phase then
    values ⟨j - 1, by omega⟩
  else 0

theorem measurable_scheduledResetPrefixPhaseVariable
    (phase j : ℕ) :
    Measurable (scheduledResetPrefixPhaseVariable phase j) := by
  unfold scheduledResetPrefixPhaseVariable
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

theorem scheduledResetPrefixPhaseVariable_apply
    (q : VolumeParams) (phase j : ℕ)
    (hj1 : 1 ≤ j) (hjphase : j ≤ phase)
    (trace : ScheduledBalancedCoolingTrace q.n) :
    scheduledResetPrefixPhaseVariable phase j
        (scheduledResetPrefixCoordinates q phase trace) =
      scheduledBalancedTracePhaseVariable q j trace := by
  simp only [scheduledResetPrefixPhaseVariable, hj1, hjphase, and_self,
    dite_true, scheduledResetPrefixCoordinates]
  congr 2
  omega

/-- The first-truncated phase coordinate, expressed solely on the finite
score prefix. -/
noncomputable def scheduledResetPrefixTruncatedPhase
    (q : VolumeParams) (I : VolumeInput q.n) (phase : ℕ) :
    ℕ → (Fin phase → ℝ) → ℝ :=
  dependentTruncatedPhase (figureOneDependentAlpha q)
    (scheduledFigureOneTraceRawMean q I)
    (scheduledResetPrefixPhaseVariable phase)

theorem measurable_scheduledResetPrefixTruncatedPhase
    (q : VolumeParams) (I : VolumeInput q.n) (phase j : ℕ) :
    Measurable (scheduledResetPrefixTruncatedPhase q I phase j) :=
  (measurable_scheduledResetPrefixPhaseVariable phase j).min measurable_const

/-- The recursively truncated accumulated product, expressed solely on the
finite score prefix. -/
noncomputable def scheduledResetPrefixTruncatedProduct
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ) :
    (Fin phase → ℝ) → ℝ :=
  dependentTruncatedProduct (figureOneDependentAlpha q)
    (scheduledFigureOneTraceTruncatedMean q I)
    (scheduledResetPrefixTruncatedPhase q I phase) i

theorem measurable_scheduledResetPrefixTruncatedProduct
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ) :
    Measurable (scheduledResetPrefixTruncatedProduct q I phase i) :=
  measurable_dependentTruncatedProduct
    (figureOneDependentAlpha q)
    (scheduledFigureOneTraceTruncatedMean q I)
    (scheduledResetPrefixTruncatedPhase q I phase)
    (measurable_scheduledResetPrefixTruncatedPhase q I phase) i

/-- For a completed coordinate, the trace-side first truncation factors
through the finite reset prefix. -/
theorem scheduledFigureOneTraceTruncatedPhase_factor_prefix
    (q : VolumeParams) (I : VolumeInput q.n) (phase j : ℕ)
    (hj1 : 1 ≤ j) (hjphase : j ≤ phase) :
    scheduledFigureOneTraceTruncatedPhase q I j =
      scheduledResetPrefixTruncatedPhase q I phase j ∘
        scheduledResetPrefixCoordinates q phase := by
  funext trace
  unfold scheduledFigureOneTraceTruncatedPhase
    scheduledResetPrefixTruncatedPhase dependentTruncatedPhase
  simp only [Function.comp_apply]
  rw [scheduledResetPrefixPhaseVariable_apply q phase j hj1 hjphase trace]

/-- The complete CV18 recursively truncated product through coordinate `i`
factors through any reset prefix containing those `i` coordinates. -/
theorem dependentTruncatedProduct_scheduledTrace_factor_prefix
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ)
    (hi : i ≤ phase) :
    dependentTruncatedProduct (figureOneDependentAlpha q)
        (scheduledFigureOneTraceTruncatedMean q I)
        (scheduledFigureOneTraceTruncatedPhase q I) i =
      scheduledResetPrefixTruncatedProduct q I phase i ∘
        scheduledResetPrefixCoordinates q phase := by
  induction i with
  | zero => rfl
  | succ i ih =>
      funext trace
      change dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledFigureOneTraceTruncatedPhase q I) (i + 1) trace =
        dependentTruncatedProduct (figureOneDependentAlpha q)
          (scheduledFigureOneTraceTruncatedMean q I)
          (scheduledResetPrefixTruncatedPhase q I phase) (i + 1)
            (scheduledResetPrefixCoordinates q phase trace)
      rw [dependentTruncatedProduct_succ,
        dependentTruncatedProduct_succ]
      have hi' : i ≤ phase := by omega
      have hcoordinate : scheduledFigureOneTraceTruncatedPhase q I (i + 1) =
          scheduledResetPrefixTruncatedPhase q I phase (i + 1) ∘
            scheduledResetPrefixCoordinates q phase :=
        scheduledFigureOneTraceTruncatedPhase_factor_prefix q I phase
          (i + 1) (by omega) hi
      have ih' := congrFun (ih hi') trace
      rw [ih', congrFun hcoordinate trace]
      rfl

/-- Concrete recurrence consumer: exact preservation of the completed score
prefix transports every earlier trace-side Lemma 7.17(c) fact unchanged. -/
theorem ApproxIndepFun.scheduledTrace_of_resetPrefix_map_eq
    (q : VolumeParams) (I : VolumeInput q.n) (phase i : ℕ)
    (hi : i < phase)
    (source reference : Measure (ScheduledBalancedCoolingTrace q.n))
    (hlaw : reference.map (scheduledResetPrefixCoordinates q phase) =
      source.map (scheduledResetPrefixCoordinates q phase))
    {epsilon : ℝ}
    (hind : ApproxIndepFun epsilon
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (scheduledFigureOneTraceTruncatedMean q I)
        (scheduledFigureOneTraceTruncatedPhase q I) i)
      (scheduledFigureOneTraceTruncatedPhase q I (i + 1)) source) :
    ApproxIndepFun epsilon
      (dependentTruncatedProduct (figureOneDependentAlpha q)
        (scheduledFigureOneTraceTruncatedMean q I)
        (scheduledFigureOneTraceTruncatedPhase q I) i)
      (scheduledFigureOneTraceTruncatedPhase q I (i + 1)) reference := by
  rw [dependentTruncatedProduct_scheduledTrace_factor_prefix q I phase i hi.le,
    scheduledFigureOneTraceTruncatedPhase_factor_prefix q I phase (i + 1)
      (by omega) (by omega)] at hind ⊢
  exact ApproxIndepFun.of_shared_prefix_law source reference
    (scheduledResetPrefixCoordinates q phase)
    (scheduledResetPrefixCoordinates q phase)
    (scheduledResetPrefixTruncatedProduct q I phase i)
    (scheduledResetPrefixTruncatedPhase q I phase (i + 1))
    (measurable_scheduledResetPrefixCoordinates q phase)
    (measurable_scheduledResetPrefixCoordinates q phase)
    (measurable_scheduledResetPrefixTruncatedProduct q I phase i)
    (measurable_scheduledResetPrefixTruncatedPhase q I phase (i + 1))
    hlaw hind

#print axioms map_scheduledResetPrefixCoordinates_resetAppend_eq
#print axioms coordinate_moments_of_shared_prefix_law
#print axioms ApproxIndepFun.of_shared_prefix_law
#print axioms scheduledFigureOneTraceTruncatedPhase_factor_prefix
#print axioms dependentTruncatedProduct_scheduledTrace_factor_prefix
#print axioms ApproxIndepFun.scheduledTrace_of_resetPrefix_map_eq

end

end ArlibCommunity.Algorithms.CV18
