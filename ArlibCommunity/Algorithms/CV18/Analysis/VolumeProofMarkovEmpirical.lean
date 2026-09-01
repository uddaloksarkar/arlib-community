/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.L2Mixing

/-!
# Empirical averages along warm Markov trajectories

CV18 reuses the last point of a phase and obtains the ratio samples from one
trajectory.  The samples are therefore not independent.  This module supplies
the trajectory domination and covariance estimates needed to formalize the
paper's dependent-sample argument.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- Law of the current state and the sum of the next `samples` observations.
This finite accumulator is exactly the object used by CV18's ratio estimator
and avoids introducing an irrelevant infinite trajectory. -/
noncomputable def markovSumLaw (P : Kernel S S) (f : S → ℝ) :
    ℕ → Measure S → Measure (S × ℝ)
  | 0, mu => mu.map fun x => (x, 0)
  | samples + 1, mu =>
      (markovSumLaw P f samples mu).bind fun stateSum =>
        (P stateSum.1).map fun next => (next, stateSum.2 + f next)

theorem measurable_markovSumStep (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) :
    Measurable fun stateSum : S × ℝ =>
      (P stateSum.1).map fun next => (next, stateSum.2 + f next) := by
  apply ArlibCommunity.Algorithms.CV18.measurable_measure_map_param_variable
  · exact P.measurable.comp measurable_fst
  · intro stateSum
    infer_instance
  exact measurable_snd.prodMk
    ((measurable_snd.comp measurable_fst).add (hf.comp measurable_snd))

theorem markovSumLaw_isProbabilityMeasure
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) (mu : Measure S) [IsProbabilityMeasure mu] :
    ∀ samples, IsProbabilityMeasure (markovSumLaw P f samples mu) := by
  intro samples
  induction samples with
  | zero =>
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  | succ samples ih =>
      simp only [markovSumLaw]
      let _ : IsProbabilityMeasure (markovSumLaw P f samples mu) := ih
      apply MeasureTheory.isProbabilityMeasure_bind
        (measurable_markovSumStep P hf).aemeasurable
      filter_upwards with stateSum
      exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Initial-law domination is preserved by the complete finite dependent
sampling experiment. -/
theorem markovSumLaw_le_smul_of_le_smul
    (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) {mu pi : Measure S}
    {M : ENNReal} (h : mu ≤ M • pi) : ∀ samples,
    markovSumLaw P f samples mu ≤ M • markovSumLaw P f samples pi := by
  intro samples
  induction samples with
  | zero =>
      exact (Measure.map_mono_of_aemeasurable h (by fun_prop)).trans_eq
        (Measure.map_smul _ _ _)
  | succ samples ih =>
      simp only [markovSumLaw]
      let Q : S × ℝ → Measure (S × ℝ) := fun stateSum =>
        (P stateSum.1).map fun next => (next, stateSum.2 + f next)
      have hQ : Measurable Q := measurable_markovSumStep P hf
      calc
        (markovSumLaw P f samples mu).bind Q ≤
            (M • markovSumLaw P f samples pi).bind Q :=
          ArlibCommunity.Algorithms.CV18.measure_bind_mono_left ih hQ
        _ = M • (markovSumLaw P f samples pi).bind Q := by
          rw [Measure.bind_smul]

/-- Warmness therefore controls every failure event of the complete dependent
finite sampling experiment. -/
theorem markovSumLaw_le_smul_of_isWarm
    (P : Kernel S S) [IsMarkovKernel P]
    {f : S → ℝ} (hf : Measurable f) {mu pi : Measure S}
    {M : ENNReal} (h : Arlib.IsWarm M mu pi) (samples : ℕ) :
    markovSumLaw P f samples mu ≤ M • markovSumLaw P f samples pi :=
  markovSumLaw_le_smul_of_le_smul P hf
    ((isWarm_iff_le_smul _ _).1 h) samples

/-- Real-valued Cauchy--Schwarz in the form used for Markov correlations. -/
theorem integral_mul_le_sqrt_mul_sqrt {pi : Measure S}
    {f g : S → ℝ} (hf : MemLp f 2 pi) (hg : MemLp g 2 pi) :
    (∫ x, f x * g x ∂pi) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂pi) *
        Real.sqrt (∫ x, g x ^ 2 ∂pi) := by
  have hprod : Integrable (fun x => f x * g x) pi := hf.integrable_mul hg
  have habsprod : Integrable (fun x => ‖f x‖ * ‖g x‖) pi :=
    hf.norm.integrable_mul hg.norm
  have hf' : MemLp f (ENNReal.ofReal 2) pi := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal 2) pi := by simpa using hg
  calc
    (∫ x, f x * g x ∂pi) ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂pi := by
      apply integral_mono_ae hprod habsprod
      filter_upwards with x
      simpa [Real.norm_eq_abs, abs_mul] using le_abs_self (f x * g x)
    _ ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂pi) ^ (1 / 2 : ℝ) *
          (∫ x, ‖g x‖ ^ (2 : ℝ) ∂pi) ^ (1 / 2 : ℝ) :=
      integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hg'
    _ = Real.sqrt (∫ x, f x ^ 2 ∂pi) *
          Real.sqrt (∫ x, g x ^ 2 ∂pi) := by
      simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

/-- Correlations of a centered observable decay at the `L²` mixing rate.
This is the dependent-sample estimate used in the variance calculation for
CV18's empirical ratio and covariance estimators. -/
theorem integral_mul_markovIter_le
    {P : Kernel S S} [IsMarkovKernel P] {pi : Measure S}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    (hpsd : HasNonnegSpectrum P pi) {f : S → ℝ}
    (hf : Measurable f) (hmem : MemLp f 2 pi)
    (hmean : ∫ x, f x ∂pi = 0) (t : ℕ) :
    (∫ x, f x * markovIter P f t x ∂pi) ≤
      |1 - spectralGap P pi| ^ t * varianceReal pi f := by
  have hTmem : MemLp (markovIter P f t) 2 pi :=
    memLp_markovIter hrev.invariant hf hmem t
  have hTmean : ∫ x, markovIter P f t x ∂pi = 0 := by
    rw [integral_markovIter hrev hf hmem t, hmean]
  have hfsq : ∫ x, f x ^ 2 ∂pi = varianceReal pi f := by
    rw [varianceReal_eq_sub hmem, hmean]
    ring
  have hTsq : ∫ x, markovIter P f t x ^ 2 ∂pi =
      varianceReal pi (markovIter P f t) := by
    rw [varianceReal_eq_sub hTmem, hTmean]
    ring
  have hv := varianceReal_markovIter_le hrev hpsd hf hmem t
  calc
    (∫ x, f x * markovIter P f t x ∂pi)
        ≤ Real.sqrt (∫ x, f x ^ 2 ∂pi) *
            Real.sqrt (∫ x, markovIter P f t x ^ 2 ∂pi) :=
          integral_mul_le_sqrt_mul_sqrt hmem hTmem
    _ = Real.sqrt (varianceReal pi f) *
          Real.sqrt (varianceReal pi (markovIter P f t)) := by rw [hfsq, hTsq]
    _ ≤ Real.sqrt (varianceReal pi f) *
          Real.sqrt ((((1 - spectralGap P pi) ^ 2) ^ t) * varianceReal pi f) := by
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv) (Real.sqrt_nonneg _)
    _ = Real.sqrt (varianceReal pi f) *
          (|1 - spectralGap P pi| ^ t * Real.sqrt (varianceReal pi f)) := by
          congr 1
          rw [Real.sqrt_mul (by positivity), ← pow_mul, Nat.mul_comm 2 t,
            pow_mul, Real.sqrt_sq_eq_abs, abs_pow]
    _ = |1 - spectralGap P pi| ^ t * varianceReal pi f := by
          calc
            Real.sqrt (varianceReal pi f) *
                (|1 - spectralGap P pi| ^ t * Real.sqrt (varianceReal pi f)) =
                |1 - spectralGap P pi| ^ t *
                  (Real.sqrt (varianceReal pi f) * Real.sqrt (varianceReal pi f)) := by ring
            _ = |1 - spectralGap P pi| ^ t * varianceReal pi f := by
              rw [Real.mul_self_sqrt (varianceReal_nonneg pi f)]

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.markovSumLaw_le_smul_of_isWarm
#print axioms Arlib.MarkovChains.markovSumLaw_isProbabilityMeasure
#print axioms Arlib.MarkovChains.integral_mul_le_sqrt_mul_sqrt
#print axioms Arlib.MarkovChains.integral_mul_markovIter_le
