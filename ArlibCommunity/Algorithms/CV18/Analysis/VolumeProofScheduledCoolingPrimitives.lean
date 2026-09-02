/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledParameters
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledExecutable

/-! # Executable cooling primitives at schedule-targeted geometry

This module is the executable transport missing from the analytic scheduled
radius development.  In particular, changing `BalancedCoolingParameters`
alone does not change the body or proposal radius used by the sampler.  The
definitions below call `scheduledBalancedAccuracyRetryCollect` directly.
-/

namespace ArlibCommunity.Algorithms.CV18

/-- One averaged Gaussian cooling phase driven by the scheduled-body sampler. -/
noncomputable def scheduledBalancedCoolingRatioEstimate
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 tau2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollect q sigma2
      (gaussianRatioWeight sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2)
      (accuracyScaleFactor q • current)).bind fun result =>
    .pure (balancedCoolingAverage (figureOnePhaseSampleCount q sigma2) result)

/-- The scheduled terminal Gaussian-to-uniform phase, retaining its endpoint. -/
noncomputable def scheduledBalancedCoolingUniformEstimateWithState
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  (scheduledBalancedAccuracyRetryCollect q sigma2 (uniformRatioWeight sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q)
      (accuracyScaleFactor q • current)).bind fun result =>
    .pure (balancedCoolingAverage (figureOneSampleCount q) result)

/-- Forget the retained endpoint after the scheduled terminal phase. -/
noncomputable def scheduledBalancedCoolingUniformRatioEstimate
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (sigma2 : ℝ) (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option ℝ) :=
  (scheduledBalancedCoolingUniformEstimateWithState parameters q sigma2 current).bind
    fun result => .pure (balancedCoolingForgetState result)

/-- Actual scheduled-body implementation of the Figure-One cooling interface. -/
noncomputable def scheduledBalancedCoolingPrimitives
    (parameters : BalancedCoolingParameters) : VolumeCoolingPrimitives where
  initialSample := figureOneInitialSample
  ratioEstimate := scheduledBalancedCoolingRatioEstimate parameters
  uniformRatioEstimate := scheduledBalancedCoolingUniformRatioEstimate parameters

/-- The finite scheduled-body Figure-One base program. -/
noncomputable def figureOneScheduledBalancedBaseProgram (q : VolumeParams) :
    MembershipOracleProgram q.n ℝ :=
  baseVolumeCooling
    (scheduledBalancedCoolingPrimitives figureOneScheduledBalancedParameters)
    explicitVolumeCoolingSchedule q

/-- Install the same single whole-run cutoff used by the global analysis. -/
noncomputable def figureOneScheduledGloballyCappedBalancedBaseProgram
    (q : VolumeParams) : MembershipOracleProgram q.n (Option ℝ) :=
  (figureOneScheduledBalancedBaseProgram q).withQueryCap
    (figureOneGlobalQueryBudget q)

theorem figureOneScheduledGloballyCappedBalancedBaseProgram_queryBound
    (q : VolumeParams) :
    (figureOneScheduledGloballyCappedBalancedBaseProgram q).QueryBound
      (figureOneGlobalQueryBudget q) := by
  exact MembershipOracleProgram.withQueryCap_queryBound _ _

#print axioms figureOneScheduledGloballyCappedBalancedBaseProgram_queryBound

end ArlibCommunity.Algorithms.CV18
