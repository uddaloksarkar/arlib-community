/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryProgram
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofMeasureApproximation
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofCappedDominance

/-!
# Approximation of finite balanced retries

This file separates cap failure from the successful payload of an optional
probability law.  It is the measure-theoretic decomposition used to compare a
capped proper-speedy block with its uncapped stationary counterpart.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

theorem MeasureLeUpTo.of_le_add
    {A : Type*} [MeasurableSpace A]
    {mu nu error : Measure A} {delta : ENNReal}
    (hle : mu ≤ nu + error) (hmass : error Set.univ ≤ delta) :
    MeasureLeUpTo mu nu delta :=
  ⟨error, hle, hmass⟩

theorem MeasureLeUpTo.map
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu nu : Measure A} {delta : ENNReal} (h : MeasureLeUpTo mu nu delta)
    {f : A → B} (hf : Measurable f) :
    MeasureLeUpTo (mu.map f) (nu.map f) delta := by
  obtain ⟨error, hle, hmass⟩ := h
  refine ⟨error.map f, ?_, ?_⟩
  · calc
      mu.map f ≤ (nu + error).map f := Measure.map_mono hle hf
      _ = nu.map f + error.map f := Measure.map_add nu error hf
  · rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]
    exact hmass

theorem MeasureLeUpTo.trans
    {A : Type*} [MeasurableSpace A]
    {mu nu xi : Measure A} {delta eta : ENNReal}
    (h₁ : MeasureLeUpTo mu nu delta)
    (h₂ : MeasureLeUpTo nu xi eta) :
    MeasureLeUpTo mu xi (delta + eta) := by
  obtain ⟨error₁, hle₁, hmass₁⟩ := h₁
  obtain ⟨error₂, hle₂, hmass₂⟩ := h₂
  refine ⟨error₁ + error₂, ?_, ?_⟩
  · calc
      mu ≤ nu + error₁ := hle₁
      _ ≤ (xi + error₂) + error₁ := add_le_add hle₂ le_rfl
      _ = xi + (error₁ + error₂) := by ac_rfl
  · rw [Measure.add_apply]
    exact add_le_add hmass₁ hmass₂

/-- Continuous Markov iteration is application of the corresponding kernel
power to the initial measure. -/
theorem iterate_eq_pow_bind
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (mu : Measure S) :
    ∀ t, Arlib.MarkovChains.iterate P mu t = mu.bind (P ^ t) := by
  intro t
  induction t with
  | zero =>
      simp only [Arlib.MarkovChains.iterate_zero, pow_zero]
      exact Measure.id_comp.symm
  | succ t ih =>
      rw [Arlib.MarkovChains.iterate_succ, ih, pow_succ']
      unfold Arlib.MarkovChains.step
      rw [Measure.bind_bind (P ^ t).measurable.aemeasurable
        P.measurable.aemeasurable]
      apply Measure.bind_congr_right
      filter_upwards with state
      exact (Kernel.comp_apply P (P ^ t) state).symm

theorem iterate_pow_one
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (mu : Measure S) (t : ℕ) :
    Arlib.MarkovChains.iterate (P ^ t) mu 1 =
      Arlib.MarkovChains.iterate P mu t := by
  rw [iterate_eq_pow_bind (P ^ t) mu 1,
    iterate_eq_pow_bind P mu t, pow_one]

noncomputable def optionSnd {S : Type*} : Option (ℝ × S) → Option S
  | none => none
  | some output => some output.2

theorem measurable_optionSnd {S : Type*} [MeasurableSpace S] :
    Measurable (optionSnd : Option (ℝ × S) → Option S) := by
  convert Measurable.optionElim none (measurable_some.comp measurable_snd) using 1
  ext value
  cases value <;> rfl

/-- The endpoint marginal of a front-recursive collector is the corresponding
ordinary Markov iterate. -/
theorem bind_frontMarkovCollectLaw_map_snd
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {f : S → ℝ}
    (hf : Measurable f) (samples : ℕ) (mu : Measure S) :
    (mu.bind (frontMarkovCollectLaw P f samples)).map Prod.snd =
      Arlib.MarkovChains.iterate P mu samples := by
  rw [bind_frontMarkovCollectLaw_eq_markovSumLaw_map_swap P hf samples mu]
  rw [Measure.map_map measurable_snd (by fun_prop)]
  convert Arlib.MarkovChains.markovSumLaw_map_fst P hf mu samples using 1
  ext stateSum
  rfl

/-- If the successful payload of an optional law is dominated by `nu`, then
the whole law is dominated by `nu.map some` plus precisely its failure mass
at `none`. -/
theorem optionMeasure_le_map_some_add_failure
    {A : Type*} [MeasurableSpace A]
    (L : Measure (Option A)) (nu : Measure A)
    (hdom : ∀ S, MeasurableSet S → L (optionSomeEvent S) ≤ nu S) :
    L ≤ nu.map some + L {none} • Measure.dirac none := by
  apply Measure.le_iff.mpr
  intro S hS
  have hpre : MeasurableSet (some ⁻¹' S) := measurable_some hS
  have hmap : nu.map some S = nu (some ⁻¹' S) :=
    Measure.map_apply measurable_some hS
  by_cases hnone : none ∈ S
  · have hset : S = optionSomeEvent (some ⁻¹' S) ∪ {none} := by
      ext value
      cases value with
      | none => simp [hnone, optionSomeEvent]
      | some value => simp [optionSomeEvent]
    have hdisjoint : Disjoint (optionSomeEvent (some ⁻¹' S)) ({none} : Set (Option A)) := by
      rw [Set.disjoint_left]
      intro value hvalue hnoneValue
      have heq : value = none := by simpa using hnoneValue
      subst value
      simpa [optionSomeEvent] using hvalue
    have hsplit : L S = L (optionSomeEvent (some ⁻¹' S)) + L {none} := by
      calc
        L S = L (optionSomeEvent (some ⁻¹' S) ∪ {none}) := congrArg L hset
        _ = L (optionSomeEvent (some ⁻¹' S)) + L {none} :=
          measure_union hdisjoint measurableSet_option_none
    have herr : (L {none} • Measure.dirac none) S = L {none} := by
      rw [Measure.smul_apply, Measure.dirac_apply' _ hS]
      simp [hnone]
    rw [Measure.add_apply, herr, hmap]
    rw [hsplit]
    exact add_le_add (hdom _ hpre) le_rfl
  · have hset : S = optionSomeEvent (some ⁻¹' S) := by
      ext value
      cases value with
      | none => simp [hnone, optionSomeEvent]
      | some value => simp [optionSomeEvent]
    have herr : (L {none} • Measure.dirac none) S = 0 := by
      rw [Measure.smul_apply, Measure.dirac_apply' _ hS]
      simp [hnone]
    rw [Measure.add_apply, herr, add_zero, hmap, hset]
    exact hdom _ hpre

/-- Additive-domination form of `optionMeasure_le_map_some_add_failure`. -/
theorem optionMeasure_leUpTo_map_some
    {A : Type*} [MeasurableSpace A]
    (L : Measure (Option A)) (nu : Measure A) {delta : ENNReal}
    (hdom : ∀ S, MeasurableSet S → L (optionSomeEvent S) ≤ nu S)
    (hfail : L {none} ≤ delta) :
    MeasureLeUpTo L (nu.map some) delta := by
  refine MeasureLeUpTo.of_le_add
    (optionMeasure_le_map_some_add_failure L nu hdom) ?_
  change L {none} * (Measure.dirac none) Set.univ ≤ delta
  rw [measure_univ, mul_one]
  exact hfail

/-- A capped one-sample proper block differs from its uncapped lazy-speedy
counterpart only through the explicit `none` failure outcome. -/
theorem bind_balancedAccuracyRetryBlockKernel_leUpTo_uncapped
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (mu : Measure (AmbientSpace q.n)) {capError : ENNReal}
    (hfail :
      (mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
          {none} ≤ capError) :
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
    let f := accuracyImportanceWeight q I sigma2 (fun _ => 0)
    MeasureLeUpTo
      (mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
      ((mu.bind <| frontMarkovCollectLaw
        (P ^ properStride) f 1).map some)
      capError := by
  dsimp only
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let K := accuracyPhaseTruncatedBody q I sigma2
  let delta := figureOneProposalRadius q sigma2
  let Q := Arlib.MarkovChains.lazyProperProposalGaussianAux K
    (accuracyPhaseTruncatedBody_measurable q I sigma2) delta sigma2
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian K delta sigma2)
  let f := accuracyImportanceWeight q I sigma2 (fun _ => 0)
  let L := mu.bind
    (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride)
  let nu := mu.bind <| frontMarkovCollectLaw
    (P ^ properStride) f 1
  have hdom : ∀ A, MeasurableSet A → L (optionSomeEvent A) ≤ nu A := by
    intro A hA
    dsimp only [L, nu, balancedAccuracyRetryBlockKernel]
    simpa [K, delta, Q, P, f] using
      (bind_cappedProperCollectLaw_optionSomeEvent_le_frontMarkovCollectLaw
        K (accuracyPhaseTruncatedBody_measurable q I sigma2) delta sigma2
        (measurable_accuracyImportanceWeight q I sigma2 measurable_const)
        proposalCap properStride 1 mu hA)
  exact optionMeasure_leUpTo_map_some L nu hdom (by simpa [L] using hfail)

/-- Endpoint-only form of the capped-block comparison. -/
theorem bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_uncapped
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (mu : Measure (AmbientSpace q.n)) {capError : ENNReal}
    (hfail :
      (mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
          {none} ≤ capError) :
    let P := Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.speedyMetropolisGaussian
        (accuracyPhaseTruncatedBody q I sigma2)
        (figureOneProposalRadius q sigma2) sigma2)
    MeasureLeUpTo
      ((mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride)).map
          optionSnd)
      ((Arlib.MarkovChains.iterate (P ^ properStride) mu 1).map some)
      capError := by
  dsimp only
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2)
  let f := accuracyImportanceWeight q I sigma2 (fun _ => 0)
  have h := bind_balancedAccuracyRetryBlockKernel_leUpTo_uncapped
    q I hsigma2 proposalCap properStride mu hfail
  have hmap := h.map (measurable_optionSnd (S := AmbientSpace q.n))
  have hendpoint :
      (mu.bind (frontMarkovCollectLaw (P ^ properStride) f 1)).map Prod.snd =
        Arlib.MarkovChains.iterate (P ^ properStride) mu 1 :=
    bind_frontMarkovCollectLaw_map_snd (P ^ properStride)
      (measurable_accuracyImportanceWeight q I sigma2 measurable_const) 1 mu
  have hnu :
      ((mu.bind (frontMarkovCollectLaw (P ^ properStride) f 1)).map some).map
          optionSnd =
        (Arlib.MarkovChains.iterate (P ^ properStride) mu 1).map some := by
    rw [Measure.map_map measurable_optionSnd measurable_some]
    rw [show (optionSnd ∘ some : ℝ × AmbientSpace q.n →
          Option (AmbientSpace q.n)) = some ∘ Prod.snd by
      funext output
      rfl]
    rw [← Measure.map_map measurable_some measurable_snd, hendpoint]
  rw [hnu] at hmap
  exact hmap

/-- Adding the speedy mixing error to the cap failure gives a stationary
endpoint comparison for one proper block. -/
theorem bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (mu pi : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure pi]
    {capError mixError : ENNReal}
    (hfail :
      (mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
          {none} ≤ capError)
    (hmix : Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyMetropolisGaussian
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2))
        mu properStride)
      pi mixError) :
    MeasureLeUpTo
      ((mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride)).map
          optionSnd)
      (pi.map some) (capError + mixError) := by
  let P := Arlib.MarkovChains.lazy
    (Arlib.MarkovChains.speedyMetropolisGaussian
      (accuracyPhaseTruncatedBody q I sigma2)
      (figureOneProposalRadius q sigma2) sigma2)
  have hcap :=
    bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_uncapped
      q I hsigma2 proposalCap properStride mu hfail
  dsimp only at hcap
  rw [iterate_pow_one P mu properStride] at hcap
  have hmixSome : Arlib.TVLe
      ((Arlib.MarkovChains.iterate P mu properStride).map some)
      (pi.map some) mixError := hmix.map measurable_some
  exact hcap.trans (MeasureLeUpTo.of_tvLe hmixSome)

/-- Lift a probability kernel through `Option`, preserving `none` as an
absorbing failure outcome. -/
noncomputable def optionKernel
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (R : Kernel S T) : Option S → Measure (Option T)
  | none => Measure.dirac none
  | some state => (R state).map some

theorem measurable_optionKernel
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (R : Kernel S T) [IsMarkovKernel R] : Measurable (optionKernel R) := by
  have hsome : Measurable fun state => (R state).map some := by
    exact measurable_measure_map_param_variable R.measurable
      (fun state => IsMarkovKernel.isProbabilityMeasure state)
      (measurable_some.comp measurable_snd)
  convert Measurable.optionElim (Measure.dirac none) hsome using 1
  ext value
  cases value <;> rfl

instance optionKernel_isProbabilityMeasure
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (R : Kernel S T) [IsMarkovKernel R] (state : Option S) :
    IsProbabilityMeasure (optionKernel R state) := by
  cases state with
  | none =>
      change IsProbabilityMeasure (Measure.dirac (none : Option T))
      infer_instance
  | some state =>
      dsimp only [optionKernel]
      let _ : IsProbabilityMeasure (R state) :=
        IsMarkovKernel.isProbabilityMeasure state
      exact Measure.isProbabilityMeasure_map measurable_some.aemeasurable

/-- One balanced KLS observation after a capped mixing block inherits the
same additive error. -/
theorem bind_balancedAccuracyRetryBlockKernel_trial_leUpTo_stationary
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (mu pi : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure pi]
    {capError mixError : ENNReal}
    (hfail :
      (mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride))
          {none} ≤ capError)
    (hmix : Arlib.TVLe
      (Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.speedyMetropolisGaussian
            (accuracyPhaseTruncatedBody q I sigma2)
            (figureOneProposalRadius q sigma2) sigma2))
        mu properStride)
      pi mixError) :
    let R := balancedAccuracyGaussianRejectionKernel q I sigma2
    MeasureLeUpTo
      (((mu.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap properStride)).map
          optionSnd).bind (optionKernel R))
      ((pi.map some).bind (optionKernel R)) (capError + mixError) := by
  dsimp only
  letI : Fact (0 < sigma2) := ⟨hsigma2⟩
  apply MeasureLeUpTo.bind_same
    (bind_balancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary
      q I hsigma2 proposalCap properStride mu pi hfail hmix)
    (measurable_optionKernel
      (balancedAccuracyGaussianRejectionKernel q I sigma2))
  intro state
  exact optionKernel_isProbabilityMeasure
    (balancedAccuracyGaussianRejectionKernel q I sigma2) state

end ArlibCommunity.Algorithms.CV18
