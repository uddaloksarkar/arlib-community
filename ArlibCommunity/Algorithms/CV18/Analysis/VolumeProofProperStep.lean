/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.Background.Arlib.MarkovChains.Continuous.HoldingTime
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.WithDensity

/-!
# A costed proper-step kernel

This file starts the operational bridge omitted in the CV18 proof of
`lem:speedy-to-ball`.  Given a Markov kernel `Q` and a measurable success
probability `p`, `geometricCostKernel p Q` returns a pair `(N, Y)`: `N` is the
number of trials through the first success and `Y` is the next `Q`-state.  Its
joint mass is

`(1 - p x) ^ (N - 1) * p x * Q x`.

The main theorem proves that forgetting `N` gives exactly `Q`.  Thus, when
`p = ell K delta` and `Q = speedyWalk K delta`, a costed proper proposal has
exactly the speedy-walk state marginal.  This is stronger than merely calling
`1 / ell(x)` a mean waiting time: it constructs the joint cost/state kernel
that can subsequently be iterated and cut off.

The remaining trajectory theorem must identify iteration of this kernel with
the concrete raw proposal loop and prove the accumulated-cost bound.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Arlib.MarkovChains

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The `failures`-th slice of a costed proper step.  Its output cost is
`failures + 1`, and its mass is the corresponding geometric weight times the
next-state kernel. -/
noncomputable def geometricCostSlice (p : Omega → ℝ≥0∞) (Q : Kernel Omega Omega)
    [IsMarkovKernel Q] (failures : ℕ) : Kernel Omega (ℕ × Omega) :=
  (Q.map fun y => (failures + 1, y)).withDensity
    (fun x _ => (1 - p x) ^ failures * p x)

theorem measurable_geometricCostWeight {p : Omega → ℝ≥0∞} (hp : Measurable p)
    (failures : ℕ) :
    Measurable (Function.uncurry
      (fun x (_ : ℕ × Omega) => (1 - p x) ^ failures * p x)) := by
  fun_prop

/-- On an event depending only on the returned state, one geometric slice is
its scalar geometric weight times the `Q`-probability of that event. -/
theorem geometricCostSlice_apply_preimage_snd
    {p : Omega → ℝ≥0∞} (hp : Measurable p) (Q : Kernel Omega Omega)
    [IsMarkovKernel Q] (failures : ℕ) (x : Omega) {S : Set Omega}
    (hS : MeasurableSet S) :
    geometricCostSlice p Q failures x (Prod.snd ⁻¹' S) =
      ((1 - p x) ^ failures * p x) * Q x S := by
  rw [geometricCostSlice, Kernel.withDensity_apply'
    _ (measurable_geometricCostWeight hp failures)]
  rw [Kernel.map_apply _ (by fun_prop)]
  rw [setLIntegral_const]
  rw [Measure.map_apply (by fun_prop) (hS.preimage measurable_snd)]
  simp only [Set.preimage_preimage, Set.preimage_id']

/-- A proper-step kernel carrying the exact number of trials through the first
success.  The zero-success case has zero total mass; all uses below assume the
pointwise success probability is nonzero. -/
noncomputable def geometricCostKernel (p : Omega → ℝ≥0∞) (Q : Kernel Omega Omega)
    [IsMarkovKernel Q] : Kernel Omega (ℕ × Omega) :=
  Kernel.sum fun failures => geometricCostSlice p Q failures

/-- Forgetting the cost of a proper step gives exactly its next-state kernel,
pointwise at every state where the success probability is nonzero. -/
theorem geometricCostKernel_apply_preimage_snd
    {p : Omega → ℝ≥0∞} (hp : Measurable p) (hp1 : ∀ x, p x ≤ 1)
    (Q : Kernel Omega Omega) [IsMarkovKernel Q] (x : Omega) (hx : p x ≠ 0)
    {S : Set Omega} (hS : MeasurableSet S) :
    geometricCostKernel p Q x (Prod.snd ⁻¹' S) = Q x S := by
  rw [geometricCostKernel, Kernel.sum_apply'
    _ _ (hS.preimage measurable_snd)]
  simp_rw [geometricCostSlice_apply_preimage_snd hp Q _ x hS]
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_geometric]
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top (hp1 x)]
  calc
    (p x)⁻¹ * (p x * Q x S) = ((p x)⁻¹ * p x) * Q x S := by rw [mul_assoc]
    _ = Q x S := by rw [ENNReal.inv_mul_cancel hx
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hp1 x)), one_mul]

/-- If success is possible from every state, the costed proper-step kernel is
a genuine Markov kernel. -/
theorem isMarkovKernel_geometricCostKernel
    {p : Omega → ℝ≥0∞} (hp : Measurable p) (hp1 : ∀ x, p x ≤ 1)
    (hp0 : ∀ x, p x ≠ 0) (Q : Kernel Omega Omega) [IsMarkovKernel Q] :
    IsMarkovKernel (geometricCostKernel p Q) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [← Set.preimage_univ (f := @Prod.snd ℕ Omega)]
  rw [geometricCostKernel_apply_preimage_snd hp hp1 Q x (hp0 x)
    MeasurableSet.univ]
  exact measure_univ

/-- Kernel-level form of the state-marginal theorem. -/
theorem geometricCostKernel_snd
    {p : Omega → ℝ≥0∞} (hp : Measurable p) (hp1 : ∀ x, p x ≤ 1)
    (hp0 : ∀ x, p x ≠ 0) (Q : Kernel Omega Omega) [IsMarkovKernel Q] :
    Kernel.snd (geometricCostKernel p Q) = Q := by
  letI : IsMarkovKernel (geometricCostKernel p Q) :=
    isMarkovKernel_geometricCostKernel hp hp1 hp0 Q
  ext x S hS
  rw [Kernel.snd_apply' _ _ hS]
  exact geometricCostKernel_apply_preimage_snd hp hp1 Q x (hp0 x) hS

/-- Exact joint law of the trial count and next state.  A returned cost of
`n + 1` has geometric weight `(1 - p x)^n * p x`, independently multiplied by
the `Q`-law of the returned state. -/
theorem geometricCostSlice_apply_rectangle
    {p : Omega → ℝ≥0∞} (hp : Measurable p) (Q : Kernel Omega Omega)
    [IsMarkovKernel Q] (m n : ℕ) (x : Omega) {S : Set Omega}
    (hS : MeasurableSet S) :
    geometricCostSlice p Q m x ({n + 1} ×ˢ S) =
      if m = n then ((1 - p x) ^ n * p x) * Q x S else 0 := by
  rw [geometricCostSlice, Kernel.withDensity_apply'
    _ (measurable_geometricCostWeight hp m)]
  rw [Kernel.map_apply _ (by fun_prop)]
  rw [setLIntegral_const]
  rw [Measure.map_apply (by fun_prop)
    ((MeasurableSet.singleton (n + 1)).prod hS)]
  by_cases hmn : m = n
  · subst m
    simp
  · simp [hmn]

theorem geometricCostKernel_apply_rectangle
    {p : Omega → ℝ≥0∞} (hp : Measurable p) (Q : Kernel Omega Omega)
    [IsMarkovKernel Q] (n : ℕ) (x : Omega) {S : Set Omega}
    (hS : MeasurableSet S) :
    geometricCostKernel p Q x ({n + 1} ×ˢ S) =
      ((1 - p x) ^ n * p x) * Q x S := by
  rw [geometricCostKernel, Kernel.sum_apply' _ _
    ((MeasurableSet.singleton (n + 1)).prod hS)]
  simp_rw [geometricCostSlice_apply_rectangle hp Q _ n x hS]
  rw [tsum_ite_eq n]

/-- The cost integral of one geometric slice. -/
theorem geometricCostSlice_lintegral_fst
    {p : Omega → ℝ≥0∞} (hp : Measurable p) (Q : Kernel Omega Omega)
    [IsMarkovKernel Q] (n : ℕ) (x : Omega) :
    ∫⁻ z, (z.1 : ℝ≥0∞) ∂geometricCostSlice p Q n x =
      (n + 1 : ℝ≥0∞) * ((1 - p x) ^ n * p x) := by
  rw [geometricCostSlice, Kernel.lintegral_withDensity _
    (measurable_geometricCostWeight hp n) _ (by fun_prop)]
  rw [Kernel.lintegral_map _ (by fun_prop) _ (by fun_prop)]
  simp only
  rw [lintegral_const, measure_univ, mul_one]
  norm_num
  ring

/-- Exact expected-cost series for a proper step.  This is the geometric
trials-including-success series; the next arithmetic lemma will identify it
with `p x` inverse. -/
theorem geometricCostKernel_lintegral_fst_eq_tsum
    {p : Omega → ℝ≥0∞} (hp : Measurable p) (Q : Kernel Omega Omega)
    [IsMarkovKernel Q] (x : Omega) :
    ∫⁻ z, (z.1 : ℝ≥0∞) ∂geometricCostKernel p Q x =
      ∑' n : ℕ, (n + 1 : ℝ≥0∞) * ((1 - p x) ^ n * p x) := by
  rw [geometricCostKernel, Kernel.sum_apply]
  rw [lintegral_sum_measure]
  exact tsum_congr fun n => geometricCostSlice_lintegral_fst hp Q n x

/-- The trials-including-success geometric series has mean `p⁻¹`. -/
theorem ennreal_geometric_trials_tsum {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp1 : p ≤ 1) :
    ∑' n : ℕ, (n + 1 : ℝ≥0∞) * ((1 - p) ^ n * p) = p⁻¹ := by
  have hptop : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  let r : ℝ := p.toReal
  have hr0 : 0 < r := ENNReal.toReal_pos hp0 hptop
  have hr1 : r ≤ 1 := by
    exact (ENNReal.toReal_le_toReal hptop ENNReal.one_ne_top).2 hp1
  have hq : ‖1 - r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hA : HasSum (fun n : ℕ => ((n : ℝ) * (1 - r) ^ n) * r)
      ((1 - r) / (1 - (1 - r)) ^ 2 * r) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hq).mul_right r
  have hB : HasSum (fun n : ℕ => (1 - r) ^ n * r) 1 := by
    have hB0 : HasSum (fun n : ℕ => (1 - r) ^ n * r) (r⁻¹ * r) := by
      simpa only [show (1 : ℝ) - (1 - r) = r by ring] using
        (hasSum_geometric_of_norm_lt_one hq).mul_right r
    convert hB0 using 1
    field_simp
  have hAB := hA.add hB
  have hsum : HasSum
      (fun n : ℕ => ((n : ℝ) + 1) * ((1 - r) ^ n * r)) (1 / r) := by
    convert hAB using 1
    · ext n
      ring
    · field_simp [hr0.ne']
      ring
  have hinv : p⁻¹ = ENNReal.ofReal (1 / r) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hr0, ENNReal.ofReal_toReal hptop]
  rw [hinv]
  rw [← hsum.tsum_eq]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable]
  apply tsum_congr
  intro n
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by linarith),
    ENNReal.ofReal_add (by positivity), ENNReal.ofReal_one]
  norm_num
  rw [show ENNReal.ofReal r = p from ENNReal.ofReal_toReal hptop]
  rw [show ENNReal.ofReal (1 - r) = 1 - p by
    rw [ENNReal.ofReal_sub 1 hr0.le, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal hptop]]
  norm_num

/-- Exact mean number of trials through the first success. -/
theorem geometricCostKernel_lintegral_fst
    {p : Omega → ℝ≥0∞} (hp : Measurable p) (hp1 : ∀ x, p x ≤ 1)
    (Q : Kernel Omega Omega) [IsMarkovKernel Q] (x : Omega) (hx : p x ≠ 0) :
    ∫⁻ z, (z.1 : ℝ≥0∞) ∂geometricCostKernel p Q x = (p x)⁻¹ := by
  rw [geometricCostKernel_lintegral_fst_eq_tsum hp Q x]
  exact ennreal_geometric_trials_tsum hx (hp1 x)

section BallWalk

variable {n : ℕ}

/-- The uniform ball-walk proper-proposal kernel: geometric waiting cost with
success probability equal to local conductance, followed by one speedy step.
CV18 uses this proposal conditioning together with a Gaussian Metropolis
filter; that specialization is a subsequent layer. -/
noncomputable def ballWalkProperStepWithCost
    (K : Set (EuclideanSpace ℝ (Fin n))) (delta : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (ℕ × EuclideanSpace ℝ (Fin n)) :=
  geometricCostKernel (ell K delta) (speedyWalk K delta)

/-- The state returned by a costed proper proposal is exactly one speedy-walk
step.  This is the one-step stopped-kernel bridge required by CV18. -/
theorem ballWalkProperStepWithCost_stateMarginal
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ell K delta x ≠ 0)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S) :
    ballWalkProperStepWithCost K delta x (Prod.snd ⁻¹' S) =
      speedyWalk K delta x S := by
  exact geometricCostKernel_apply_preimage_snd (measurable_ell hK delta)
    (fun y => ell_le_one K delta y) (speedyWalk K delta) x hx hS

/-- The raw-proposal cost of one proper ball-walk step has the exact geometric
trials series with parameter equal to local conductance. -/
theorem ballWalkProperStepWithCost_expectedCostSeries
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ z, (z.1 : ℝ≥0∞) ∂ballWalkProperStepWithCost K delta x =
      ∑' m : ℕ, (m + 1 : ℝ≥0∞) *
        ((1 - ell K delta x) ^ m * ell K delta x) := by
  exact geometricCostKernel_lintegral_fst_eq_tsum
    (measurable_ell hK delta) (speedyWalk K delta) x

/-- Exact version of CV18's one-state waiting-time claim: at a non-stuck
state, the expected raw proposal count through the next proper proposal is
`1 / ell(x)`. -/
theorem ballWalkProperStepWithCost_expectedCost
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (delta : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ell K delta x ≠ 0) :
    ∫⁻ z, (z.1 : ℝ≥0∞) ∂ballWalkProperStepWithCost K delta x =
      (ell K delta x)⁻¹ := by
  exact geometricCostKernel_lintegral_fst (measurable_ell hK delta)
    (fun y => ell_le_one K delta y) (speedyWalk K delta) x hx

end BallWalk

end Arlib.MarkovChains
