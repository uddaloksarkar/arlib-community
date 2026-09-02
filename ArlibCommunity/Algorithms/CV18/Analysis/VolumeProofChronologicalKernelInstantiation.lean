/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofChronologicalDependentAssembly

/-!
# Concrete chronological ideal coordinates for the CV18 exact-chance argument

This module instantiates the ideal side of the chronological dependent-product
argument on the existing finite Figure-One product law.  The explicit phase
equivalence ensures that the first `figureOneDependentPhaseCount q` coordinates
are distinct and hence independent.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Reindex the existing independent ideal phase experiment chronologically. -/
noncomputable def figureOneChronologicalIdealCoordinate
    (q : VolumeParams) (j : ℕ) : FigureOneIdealExperimentSpace q → ℝ :=
  figureOneIdealCoordinate q (figureOneChronologicalPhaseAt q j)

theorem figureOneChronologicalIdealCoordinate_measurable
    (q : VolumeParams) (j : ℕ) :
    Measurable (figureOneChronologicalIdealCoordinate q j) :=
  figureOneIdealCoordinate_measurable q _

theorem figureOneChronologicalIdealCoordinate_memLp
    (q : VolumeParams) (I : VolumeInput q.n) (j : ℕ) (p : ENNReal) :
    MemLp (figureOneChronologicalIdealCoordinate q j) p
      (figureOneIdealExperimentLaw q I) :=
  figureOneIdealCoordinate_memLp q I _ p

theorem figureOneChronologicalIdealCoordinate_mean
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I) (j : ℕ) :
    (∫ samples, figureOneChronologicalIdealCoordinate q j samples
      ∂figureOneIdealExperimentLaw q I) =
        figureOneChronologicalRawMean q I j :=
  figureOneIdealCoordinate_mean q I hsharp _

theorem figureOneChronologicalIdealCoordinate_secondMoment_le
    (q : VolumeParams) (I : VolumeInput q.n)
    (hsharp : FigureOneSharpAcceleratedMoments q I) (j : ℕ) :
    (∫ samples, figureOneChronologicalIdealCoordinate q j samples ^ 2
      ∂figureOneIdealExperimentLaw q I) ≤
        figureOneChronologicalMomentFactor q j *
          figureOneChronologicalRawMean q I j ^ 2 :=
  figureOneIdealCoordinate_secondMoment_le q I hsharp _

theorem figureOneIdealPhaseEstimator_nonneg
    (q : VolumeParams) (phase : FigureOneIdealPhase q)
    (samples : FigureOneIdealPhaseSampleSpace q phase) :
    0 ≤ figureOneIdealPhaseEstimator q phase samples := by
  cases phase with
  | fixed k =>
      simp only [figureOneIdealPhaseEstimator]
      unfold idealEmpiricalAverage gaussianRatioWeight
      apply div_nonneg
      · exact Finset.sum_nonneg fun i _ => div_nonneg (Real.exp_pos _).le
          (Real.exp_pos _).le
      · positivity
  | accelerated k =>
      simp only [figureOneIdealPhaseEstimator]
      unfold idealEmpiricalAverage gaussianRatioWeight
      apply div_nonneg
      · exact Finset.sum_nonneg fun i _ => div_nonneg (Real.exp_pos _).le
          (Real.exp_pos _).le
      · positivity
  | terminal =>
      simp only [figureOneIdealPhaseEstimator]
      unfold idealEmpiricalAverage uniformRatioWeight
      apply div_nonneg
      · exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
      · positivity

theorem figureOneChronologicalIdealCoordinate_nonneg
    (q : VolumeParams) (j : ℕ) (samples : FigureOneIdealExperimentSpace q) :
    0 ≤ figureOneChronologicalIdealCoordinate q j samples :=
  figureOneIdealPhaseEstimator_nonneg q _ _

/-- Chronological coordinates are mutually independent inside their finite
horizon.  The bound is essential because `figureOneChronologicalPhaseAt` is
defined periodically outside that horizon. -/
theorem figureOneChronologicalIdealCoordinate_indepFun
    (q : VolumeParams) (I : VolumeInput q.n) {j k : ℕ}
    (hj : 1 ≤ j) (hj' : j ≤ figureOneDependentPhaseCount q)
    (hk : 1 ≤ k) (hk' : k ≤ figureOneDependentPhaseCount q)
    (hjk : j ≠ k) :
    IndepFun (figureOneChronologicalIdealCoordinate q j)
      (figureOneChronologicalIdealCoordinate q k)
      (figureOneIdealExperimentLaw q I) := by
  apply (figureOneIdealCoordinates_iIndepFun q I).indepFun
  intro heq
  apply hjk
  have hjmod : (j - 1) % figureOneDependentPhaseCount q = j - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hkmod : (k - 1) % figureOneDependentPhaseCount q = k - 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hfin : (⟨j - 1, by omega⟩ : Fin (figureOneDependentPhaseCount q)) =
      ⟨k - 1, by omega⟩ := by
    apply (figureOneChronologicalPhaseOrder q).injective
    simpa [figureOneChronologicalPhaseAt, hjmod, hkmod] using heq
  have : j - 1 = k - 1 := congrArg Fin.val hfin
  omega

#print axioms figureOneChronologicalIdealCoordinate_mean
#print axioms figureOneChronologicalIdealCoordinate_secondMoment_le
#print axioms figureOneChronologicalIdealCoordinate_indepFun

end

end ArlibCommunity.Algorithms.CV18
