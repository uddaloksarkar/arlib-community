/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCollectorEndpoint
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledInitialWarmStart

/-! # Complete scheduled phase endpoint replacement

This lifts the cap-aware one-transition exact-chance bound through every
remaining sample of a phase collector and then forgets the accumulated ratio.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open _root_.Arlib _root_.Arlib.MarkovChains

set_option maxHeartbeats 3000000 in
section

theorem measurable_iteratedKernelLaw_const_from_initial
    {X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (T : X → Measure S) (K : S → Measure S)
    (hT : Measurable T) (hK : Measurable K) :
    ∀ steps, Measurable fun x =>
      iteratedKernelLaw (fun _ => K) (T x) steps := by
  intro steps
  induction steps with
  | zero => exact hT
  | succ steps ih => exact Measure.measurable_bind' hK |>.comp ih

theorem bind_iteratedKernelLaw_const_from_initial
    {X S : Type*} [MeasurableSpace X] [MeasurableSpace S]
    (mu : Measure X) (T : X → Measure S) (K : S → Measure S)
    (hT : Measurable T) (hK : Measurable K) :
    ∀ steps,
      mu.bind (fun x => iteratedKernelLaw (fun _ => K) (T x) steps) =
        iteratedKernelLaw (fun _ => K) (mu.bind T) steps := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hprefix : Measurable fun x =>
          iteratedKernelLaw (fun _ => K) (T x) steps :=
        measurable_iteratedKernelLaw_const_from_initial T K hT hK steps
      calc
        mu.bind (fun x =>
            iteratedKernelLaw (fun _ => K) (T x) (steps + 1)) =
          mu.bind (fun x =>
            (iteratedKernelLaw (fun _ => K) (T x) steps).bind K) := rfl
        _ = (mu.bind (fun x =>
            iteratedKernelLaw (fun _ => K) (T x) steps)).bind K :=
          (Measure.bind_bind hprefix.aemeasurable hK.aemeasurable).symm
        _ = (iteratedKernelLaw (fun _ => K) (mu.bind T) steps).bind K := by
          rw [ih]
        _ = iteratedKernelLaw (fun _ => K) (mu.bind T) (steps + 1) := rfl

/-- Starting from a probability law with the concrete scheduled warmness,
the retained endpoint after a complete nonempty collector is within one
corrected transition budget per sample of the normalized accepted target. -/
theorem map_bind_figureOneFinalScheduledTransitionCollectLaw_optionSnd_leUpTo
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Measurable weight)
    (samples : ℕ) (total : ℝ)
    (rho : Measure (AmbientSpace q.n)) [IsProbabilityMeasure rho]
    (hbaseWarm : IsWarm
      (ENNReal.ofReal (8 * speedyAdjacentWarmConstant q)) rho
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) :
    let parameters := figureOneFinalScheduledBalancedParameters
    let cap := parameters.proposalCap q sigma2
    let stride := parameters.properStride q sigma2
    let retries := parameters.retryLimit q sigma2
    let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)
    MeasureLeUpTo
      ((rho.bind fun current =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
          retries (samples + 1) total current).map optionSnd)
      (target.map some)
      ((samples + 1) • figureOneCorrectedTransitionBudget q) := by
  dsimp only
  let cap := figureOneFinalScheduledBalancedParameters.proposalCap q sigma2
  let stride := figureOneFinalScheduledBalancedParameters.properStride q sigma2
  let retries := figureOneFinalScheduledBalancedParameters.retryLimit q sigma2
  let T := scheduledBalancedAccuracyTransitionLawAux q I sigma2 cap stride retries
  let K := figureOneFinalScheduledRetainedOptionKernel q I sigma2
  let target := scheduledBalancedAccuracyGaussianAcceptedTargetLaw q I sigma2
    (ellGaussianProb
      (figureOneScheduledPhaseBody q I sigma2)
      (figureOneScheduledProposalRadius q sigma2) sigma2)
  have hT := scheduledBalancedAccuracyTransitionLawAux_measurable_and_probability
    q I hsigma2 cap stride retries
  have hK := figureOneFinalScheduledRetainedOptionKernel_measurable_and_probability
    q I hsigma2
  have hcollect := scheduledBalancedTransitionCollectLaw_measurable_and_probability
    q I hsigma2 hweight cap stride retries (samples + 1)
  have hcollectCurrent : Measurable fun current : AmbientSpace q.n =>
      scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride retries
        (samples + 1) total current := by
    change Measurable
      ((fun state : ℝ × AmbientSpace q.n =>
          scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
            retries (samples + 1) state.1 state.2) ∘
        fun current => (total, current))
    exact hcollect.1.comp (measurable_const.prodMk measurable_id)
  have hsource :
      ((rho.bind fun current =>
        scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
          retries (samples + 1) total current).map optionSnd) =
        iteratedKernelLaw (fun _ => K) (rho.bind T) samples := by
    calc
      _ = rho.bind fun current =>
          (scheduledBalancedTransitionCollectLaw q I sigma2 weight cap stride
            retries (samples + 1) total current).map optionSnd :=
        map_bind_eq_bind_map_of_measurable rho hcollectCurrent
          measurable_optionSnd
      _ = rho.bind fun current =>
          iteratedKernelLaw (fun _ => K) (T current) samples := by
        apply Measure.bind_congr_right
        filter_upwards with current
        simpa [cap, stride, retries, T, K] using
          map_scheduledBalancedTransitionCollectLaw_optionSnd
            q I hsigma2 hweight samples total current
      _ = _ := bind_iteratedKernelLaw_const_from_initial rho T K
        (by simpa [T] using hT.1) (by simpa [K] using hK.1) samples
  have hfirst : MeasureLeUpTo (rho.bind T) (target.map some)
      (figureOneCorrectedTransitionBudget q) := by
    simpa [T, target, cap, stride, retries] using
      bind_figureOneFinalScheduledBalancedTransition_leUpTo_acceptedTarget
        q I hsigma2 rho hbaseWarm rho inferInstance
          ((IsWarm.refl rho).mono (by norm_num))
  have hiter := iterated_figureOneFinalScheduledRetainedOptionKernel_leUpTo
    q I hsigma2 (rho.bind T) hfirst samples
  rw [hsource]
  convert hiter using 1
  rw [succ_nsmul]
  exact add_comm _ _

#print axioms map_bind_figureOneFinalScheduledTransitionCollectLaw_optionSnd_leUpTo

end

end ArlibCommunity.Algorithms.CV18
