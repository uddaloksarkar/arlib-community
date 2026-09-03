/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryApproximation

/-!
# Second moments under killed collector domination

A finite executable collector returns `none` when its local cap or retry
budget is exhausted.  The numerical estimator assigns zero to that branch.
Consequently, domination of the successful payload law is enough to transfer
its second moment: the missing mass at `none` contributes exactly zero.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- Extend a real observable on successful payloads by zero on failure. -/
def optionZeroLift {A : Type*} (f : A → ℝ) : Option A → ℝ
  | none => 0
  | some x => f x

theorem measurable_optionZeroLift
    {A : Type*} [MeasurableSpace A] {f : A → ℝ} (hf : Measurable f) :
    Measurable (optionZeroLift f) := by
  convert Measurable.optionElim (0 : ℝ) hf using 1
  funext value
  cases value <;> rfl

/-- A successful-payload measure domination transfers the square of the
zero-filled observable.  This is the exact second-moment analogue of the
optional-law decomposition used by the retry approximation layer. -/
theorem integral_optionZeroLift_sq_le_of_success_dom
    {A : Type*} [MeasurableSpace A]
    (L : Measure (Option A)) [IsFiniteMeasure L]
    (nu : Measure A) {f : A → ℝ} (hf : Measurable f)
    (hfmem : MemLp f 2 nu)
    (hdom : ∀ S, MeasurableSet S → L (optionSomeEvent S) ≤ nu S) :
    (∫ value, optionZeroLift f value ^ 2 ∂L) ≤
      ∫ x, f x ^ 2 ∂nu := by
  let error : Measure (Option A) := L {none} • Measure.dirac none
  let upper : Measure (Option A) := nu.map some + error
  have hle : L ≤ upper := by
    dsimp only [upper, error]
    exact optionMeasure_le_map_some_add_failure L nu hdom
  have hsomeSq : Integrable (fun value : Option A =>
      optionZeroLift f value ^ 2) (nu.map some) := by
    apply (integrable_map_measure
      ((measurable_optionZeroLift hf).pow_const 2).aestronglyMeasurable
      measurable_some.aemeasurable).2
    rw [show (fun value : Option A => optionZeroLift f value ^ 2) ∘ some =
        fun x => f x ^ 2 by
      funext x
      rfl]
    exact hfmem.integrable_sq
  have herrorTop : L {none} ≠ ⊤ :=
    measure_ne_top L {none}
  have herrorSq : Integrable (fun value : Option A =>
      optionZeroLift f value ^ 2) error := by
    dsimp only [error]
    have hdirac : Integrable (fun value : Option A =>
        optionZeroLift f value ^ 2) (Measure.dirac none) := by
      apply integrable_dirac'
        ((measurable_optionZeroLift hf).pow_const 2).stronglyMeasurable
      simp [optionZeroLift]
    exact hdirac.smul_measure herrorTop
  have hupperSq : Integrable (fun value : Option A =>
      optionZeroLift f value ^ 2) upper := by
    dsimp only [upper]
    exact integrable_add_measure.2 ⟨hsomeSq, herrorSq⟩
  calc
    (∫ value, optionZeroLift f value ^ 2 ∂L) ≤
        ∫ value, optionZeroLift f value ^ 2 ∂upper :=
      integral_mono_measure hle
        (Filter.Eventually.of_forall fun value => sq_nonneg _)
        hupperSq
    _ = (∫ value, optionZeroLift f value ^ 2 ∂nu.map some) +
          ∫ value, optionZeroLift f value ^ 2 ∂error := by
      dsimp only [upper]
      exact integral_add_measure hsomeSq herrorSq
    _ = (∫ x, f x ^ 2 ∂nu) + 0 := by
      congr 1
      · rw [integral_map measurable_some.aemeasurable
          ((measurable_optionZeroLift hf).pow_const 2).aestronglyMeasurable]
        rfl
      · dsimp only [error]
        rw [integral_smul_measure]
        rw [integral_dirac'
          (fun value : Option A => optionZeroLift f value ^ 2) none
          ((measurable_optionZeroLift hf).pow_const 2).stronglyMeasurable]
        simp [optionZeroLift]
    _ = ∫ x, f x ^ 2 ∂nu := add_zero _

#print axioms integral_optionZeroLift_sq_le_of_success_dom

end ArlibCommunity.Algorithms.CV18
