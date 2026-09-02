/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofApproxIndependenceMarkov
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRetryApproximation

/-!
# Balanced executable transitions and CV18 approximate independence

This module turns the one-sided finite-retry approximation into the
probability/total-variation form consumed by the Markov-history version of
CV18 Lemma 7.18.  In particular, the normalized accepted branch is proved to
be a probability measure from the same explicit acceptance lower bound used
by the retry analysis.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- The accepted target of a balanced phase is a probability law whenever
the stationary acceptance mass has the explicit positive lower bound used by
the finite-retry theorem. -/
theorem balancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (pi : Measure (AmbientSpace q.n)) [IsProbabilityMeasure pi]
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ) :
    IsProbabilityMeasure
      (balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi) := by
  let accepted := balancedAcceptedStateMeasure q I sigma2 pi
  let scale : AmbientSpace q.n -> AmbientSpace q.n := fun x =>
    (accuracyScaleFactor q)⁻¹ • x
  let acceptedTarget := accepted.map scale
  have hscale : Measurable scale := by
    dsimp only [scale]
    exact (measurable_const : Measurable fun _ : AmbientSpace q.n =>
      (accuracyScaleFactor q)⁻¹).smul measurable_id
  have haccepted0 : accepted Set.univ ≠ 0 := ne_of_gt <|
    (by norm_num : 0 < ENNReal.ofReal (7 / 128 : ℝ)).trans_le
      (by simpa [accepted] using hacceptedLower)
  have hacceptedTop : accepted Set.univ ≠ ⊤ := by
    have hle := balancedAcceptedStateMeasure_le_half_smul q I hsigma2 pi
    exact ne_top_of_le_ne_top (by simp) <|
      Measure.le_iff'.mp hle Set.univ
  have htargetMass : acceptedTarget Set.univ = accepted Set.univ := by
    dsimp only [acceptedTarget]
    rw [Measure.map_apply hscale MeasurableSet.univ, Set.preimage_univ]
  have htarget0 : acceptedTarget Set.univ ≠ 0 := by
    rw [htargetMass]
    exact haccepted0
  have htargetTop : acceptedTarget Set.univ ≠ ⊤ := by
    rw [htargetMass]
    exact hacceptedTop
  change IsProbabilityMeasure (Arlib.condOn acceptedTarget Set.univ)
  exact Arlib.isProbabilityMeasure_condOn acceptedTarget htarget0 htargetTop

/-- Total-variation form of the complete finite balanced transition.  The
error is exactly the first-block approximation plus the rejected-branch retry
error; no factor is lost when converting from additive domination because
both sides are probability measures. -/
theorem bind_balancedTransition_tvLe_acceptedTarget
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho pi : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure rho] [IsProbabilityMeasure pi]
    {firstError retryError : ENNReal}
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ)
    (hrejectedLower : (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 pi Set.univ)
    (hfirstBlock : MeasureLeUpTo
      ((rho.bind
        (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some) firstError)
    (hretryBlock :
      let rejected := balancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) retryError) :
    Arlib.TVLe
      (rho.bind
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1)))
      ((balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi).map some)
      (firstError +
        balancedRejectedStateMeasure q I sigma2 pi Set.univ *
          balancedRetryError retryError
            (balancedRejectedStateMeasure q I sigma2 pi Set.univ) attempts) := by
  let K := balancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride (attempts + 1)
  have hK := balancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 proposalCap properStride (attempts + 1)
  let _ : IsProbabilityMeasure (rho.bind K) :=
    isProbabilityMeasure_bind hK.1.aemeasurable (ae_of_all _ hK.2)
  let target := balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let _ : IsProbabilityMeasure target :=
    balancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
      q I hsigma2 pi hacceptedLower
  let _ : IsProbabilityMeasure (target.map some) :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  have hdom := bind_balancedTransition_leUpTo_acceptedTarget
    q I hsigma2 proposalCap properStride attempts rho pi
      hacceptedLower hrejectedLower hfirstBlock hretryBlock
  change Arlib.TVLe (rho.bind K) (target.map some) _
  exact hdom.to_tvLe

/-- A finite per-block error remains finite through any finite balanced retry
recurrence. -/
theorem balancedRetryError_ne_top {delta rejectMass : ENNReal}
    (hdelta : delta ≠ ⊤) (hrejectMass : rejectMass ≠ ⊤) :
    forall attempts, balancedRetryError delta rejectMass attempts ≠ ⊤ := by
  intro attempts
  induction attempts with
  | zero => simp [balancedRetryError]
  | succ attempts ih =>
      simp only [balancedRetryError]
      exact ENNReal.add_ne_top.mpr
        ⟨hdelta, ENNReal.mul_ne_top hrejectMass ih⟩

/-- Concrete adjacent-sample form of CV18 Lemma 7.18(a) for the executable
balanced transition.  Every half-mass conditioning is `2`-warm; a uniform
first-block estimate for such starts and the stationary retry estimate place
both conditional and unconditional next laws near the same accepted target.
-/
theorem approxIndepFun_balancedTransition_of_warm_blocks
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride attempts : ℕ)
    (rho pi : Measure (AmbientSpace q.n))
    [IsProbabilityMeasure rho] [IsProbabilityMeasure pi]
    {firstError retryError : ENNReal}
    (hfirstError : firstError ≠ ⊤) (hretryError : retryError ≠ ⊤)
    (hacceptedLower : ENNReal.ofReal (7 / 128 : ℝ) ≤
      balancedAcceptedStateMeasure q I sigma2 pi Set.univ)
    (hrejectedLower : (2 : ENNReal)⁻¹ ≤
      balancedRejectedStateMeasure q I sigma2 pi Set.univ)
    (hfirstBlock : forall mu : Measure (AmbientSpace q.n),
      IsProbabilityMeasure mu -> Arlib.IsWarm 2 mu rho ->
      MeasureLeUpTo
        ((mu.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) firstError)
    (hretryBlock :
      let rejected := balancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (balancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) retryError) :
    let rejectMass :=
      balancedRejectedStateMeasure q I sigma2 pi Set.univ
    let error := firstError + rejectMass *
      balancedRetryError retryError rejectMass attempts
    ApproxIndepFun (error + error).toReal Prod.fst Prod.snd
      (sequentialPairLaw rho
        (balancedAccuracyTransitionLawAux q I sigma2 proposalCap
          properStride (attempts + 1))) := by
  dsimp only
  let rejectMass := balancedRejectedStateMeasure q I sigma2 pi Set.univ
  let error := firstError + rejectMass *
    balancedRetryError retryError rejectMass attempts
  let K := balancedAccuracyTransitionLawAux q I sigma2 proposalCap
    properStride (attempts + 1)
  let target := balancedAccuracyGaussianAcceptedTargetLaw q I sigma2 pi
  let targetSome := target.map some
  have hK := balancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 proposalCap properStride (attempts + 1)
  have hrejectedTop : rejectMass ≠ ⊤ := by
    dsimp only [rejectMass]
    have hle := balancedRejectedStateMeasure_le q I sigma2 pi
    exact ne_top_of_le_ne_top (measure_ne_top pi Set.univ) <|
      Measure.le_iff'.mp hle Set.univ
  have hretryFinite :
      balancedRetryError retryError rejectMass attempts ≠ ⊤ :=
    balancedRetryError_ne_top hretryError hrejectedTop attempts
  have herror : error ≠ ⊤ := by
    dsimp only [error]
    exact ENNReal.add_ne_top.mpr
      ⟨hfirstError, ENNReal.mul_ne_top hrejectedTop hretryFinite⟩
  let _ : IsProbabilityMeasure target :=
    balancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
      q I hsigma2 pi hacceptedLower
  let _ : IsProbabilityMeasure targetSome :=
    Measure.isProbabilityMeasure_map measurable_some.aemeasurable
  apply approxIndepFun_fst_snd_sequentialPairLaw_of_warm_leUpTo
    rho hK.1 hK.2 targetSome herror
  intro mu hmu hwarm
  let _ : IsProbabilityMeasure mu := hmu
  simpa [K, targetSome, target, error, rejectMass] using
    (bind_balancedTransition_leUpTo_acceptedTarget
      q I hsigma2 proposalCap properStride attempts mu pi
        hacceptedLower hrejectedLower
        (hfirstBlock mu hmu hwarm) hretryBlock)

#print axioms balancedAccuracyGaussianAcceptedTargetLaw_isProbabilityMeasure_of_lower
#print axioms bind_balancedTransition_tvLe_acceptedTarget
#print axioms approxIndepFun_balancedTransition_of_warm_blocks

end ArlibCommunity.Algorithms.CV18
