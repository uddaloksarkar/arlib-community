/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledConcreteTransition

/-! # Final scheduled transition from the exact first-block warmness -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal Pointwise
open _root_.Arlib _root_.Arlib.MarkovChains

/-- The final transition theorem with the intermediate retained law removed:
the input itself may use the exact `16 *` first-block warmness for which the
final stride and local cap were chosen. -/
theorem bind_figureOneFinalScheduledBalancedTransition_tvLe_of_warmSixteen
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (mu : Measure (AmbientSpace q.n)) [IsProbabilityMeasure mu]
    (hwarm : Arlib.IsWarm
      (ENNReal.ofReal (16 * speedyAdjacentWarmConstant q)) mu
      (ellGaussianProb
        (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2)) :
    Arlib.TVLe
      (mu.bind
        (scheduledBalancedAccuracyTransitionLawAux q I sigma2
          (figureOneFinalScheduledBalancedParameters.proposalCap q sigma2)
          (figureOneFinalScheduledBalancedParameters.properStride q sigma2)
          (figureOneFinalScheduledBalancedParameters.retryLimit q sigma2)))
      ((truncatedGaussianProbability q I sigma2 hsigma2 :
        Measure (AmbientSpace q.n)).map some)
      (figureOneCorrectedTransitionBudget q) := by
  let attempts := figureOneSafeRetryCount q - 1
  let proposalCap :=
    figureOneFinalScheduledBalancedParameters.proposalCap q sigma2
  let properStride :=
    figureOneFinalScheduledBalancedParameters.properStride q sigma2
  let K := figureOneScheduledPhaseBody q I sigma2
  let delta := figureOneScheduledProposalRadius q sigma2
  let pi := ellGaussianProb K delta sigma2
  have hproposalCap : 0 < proposalCap := by
    simpa [proposalCap] using
      figureOneFinalScheduledBalancedParameters_proposalCap_pos q sigma2
  have hmixWithin := mixesWithin_scheduledPhaseBody_figureOne_cv18
    q I hsigma2 (M := 16 * speedyAdjacentWarmConstant q)
      (eps := figureOneCorrectedBlockMixingError q attempts)
      (by
        have hM := speedyAdjacentWarmConstant_one_le q
        nlinarith)
      (by simpa [K, delta, pi] using hwarm)
      (figureOneCorrectedBlockMixingError_pos q attempts)
      (figureOneCorrectedBlockMixingError_le_one q attempts)
      (by
        have hwalk :=
          figureOneScheduledCorrectedFirstWalkRequirement_le_stride
            q sigma2 attempts
        change figureOneScheduledWalkRequirement q sigma2
          (16 * speedyAdjacentWarmConstant q)
            (figureOneCorrectedBlockMixingError q attempts) ≤
              (properStride : ℝ)
          at hwalk
        simpa only [figureOneScheduledWalkRequirement] using hwalk)
  have hmix : Arlib.TVLe
      (iterate (lazy (speedyMetropolisGaussian K delta sigma2))
        mu properStride)
      pi (ENNReal.ofReal (figureOneCorrectedBlockMixingError q attempts)) := by
    simpa [MixesWithin, K, delta, pi, properStride, attempts] using hmixWithin
  have hfirst : MeasureLeUpTo
      ((mu.bind
        (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
          properStride)).map optionSnd)
      (pi.map some) (2 * figureOneCorrectedBlockBudget q attempts) := by
    have hblock :=
      bind_scheduledBalancedAccuracyRetryBlockKernel_endpoint_leUpTo_stationary_of_isWarm
        q I hsigma2 proposalCap properStride hproposalCap mu
          (by simpa [K, delta, pi] using hwarm)
          (by
            simpa [properStride, proposalCap, attempts] using
              figureOneFinalScheduled_firstCapBudget q sigma2)
          hmix
    have hmixEq : ENNReal.ofReal
        (figureOneCorrectedBlockMixingError q attempts) =
          figureOneCorrectedBlockBudget q attempts := rfl
    simpa [hmixEq, two_mul, K, delta, pi] using hblock
  have hretry :
      let rejected := scheduledBalancedRejectedStateMeasure q I sigma2 pi
      let rejectedProb := Arlib.condOn rejected Set.univ
      MeasureLeUpTo
        ((rejectedProb.bind
          (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
            properStride)).map optionSnd)
        (pi.map some) (2 * figureOneCorrectedBlockBudget q attempts) := by
    simpa [K, delta, pi] using
      scheduledBalancedRejectedRetryBlock_leUpTo_stationary
        q I hsigma2 proposalCap properStride attempts hproposalCap
          (by
            simpa [properStride, attempts,
              figureOneFinalScheduledBalancedParameters_properStride] using
              figureOneScheduledCorrectedRetryWalkRequirement_le_stride
                q sigma2 attempts)
          (by
            simpa [properStride, proposalCap, attempts] using
              figureOneFinalScheduled_retryCapBudget q sigma2)
  have hdelta : 0 < delta := figureOneScheduledProposalRadius_pos q hsigma2
  have hmass0 : ellGaussianMeasure K delta sigma2 Set.univ ≠ 0 := by
    dsimp [K]
    exact ellGaussianMeasure_univ_ne_zero
      (figureOneScheduledPhaseBody_measurable q I sigma2)
      (figureOneScheduledPhaseBody_convex q I sigma2)
      (figureOneScheduledPhaseBody_isCompact q I sigma2).isBounded
      (figureOneScheduledPhaseBody_volume_ne_zero q I hsigma2)
      hdelta sigma2
  have hmasstop : ellGaussianMeasure K delta sigma2 Set.univ ≠ ⊤ := by
    dsimp [K]
    exact ellGaussianMeasure_ne_top_cv18
      (figureOneScheduledPhaseBody_volume_ne_top q I sigma2) delta hsigma2
  let _ : IsProbabilityMeasure pi :=
    isProbabilityMeasure_ellGaussianProb hmass0 hmasstop
  have haccepted : ENNReal.ofReal (7 / 128 : ℝ) ≤
      scheduledBalancedAcceptedStateMeasure q I sigma2 pi Set.univ := by
    simpa [K, delta, pi] using
      scheduledBalancedAcceptedStateMeasure_mass_ge q I hsigma2
  have hreject :
      scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ ≤
        ENNReal.ofReal (121 / 128 : ℝ) :=
    scheduledBalancedRejectedStateMeasure_mass_le
      q I hsigma2 pi haccepted
  have htail :
      (scheduledBalancedRejectedStateMeasure q I sigma2 pi Set.univ) ^
          (attempts + 1) ≤ figureOneCorrectedRetryTailBudget q := by
    simpa [attempts] using figureOneSafeRetryTail_le q hreject
  have htv :=
    bind_scheduledBalancedTransition_tvLe_truncatedGaussian_corrected
      q I hsigma2 proposalCap properStride attempts mu hfirst hretry htail
  simpa [proposalCap, properStride, attempts,
    Nat.sub_add_cancel (figureOneSafeRetryCount_pos q)] using htv

#print axioms bind_figureOneFinalScheduledBalancedTransition_tvLe_of_warmSixteen

end ArlibCommunity.Algorithms.CV18
