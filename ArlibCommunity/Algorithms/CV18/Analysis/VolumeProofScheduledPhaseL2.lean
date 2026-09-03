/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledTransitionSupport

/-!
# Square-integrability of executable scheduled phase averages

The scheduled rejection test restricts every successful target to a compact
phase body.  Hence any continuous nonnegative importance weight has a common
finite bound there, uniformly in the phase starting point.  The finite
collector bound then gives the `L²` premise required by the trace moment
capstone.
-/

open MeasureTheory ProbabilityTheory

namespace ArlibCommunity.Algorithms.CV18

/-- A continuous nonnegative observable has a nonnegative upper bound on the
compact scheduled phase body. -/
theorem exists_scheduledPhaseBody_weight_upper_bound
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight)
    (hweight0 : ∀ x, 0 ≤ weight x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ figureOneScheduledPhaseBody q I sigma2,
      weight x ≤ B := by
  let K := figureOneScheduledPhaseBody q I sigma2
  obtain ⟨B, hB⟩ :=
    (figureOneScheduledPhaseBody_isCompact q I sigma2).bddAbove_image
      hweight.continuousOn
  have hzero : (0 : AmbientSpace q.n) ∈ K := by
    refine ⟨unitBall_subset_truncatedBody q I
      (Metric.mem_closedBall_self zero_le_one), ?_⟩
    exact Metric.mem_closedBall_self
      (figureOneScheduledPhaseRadius_pos q hsigma2).le
  have hB0 : 0 ≤ B :=
    (hweight0 0).trans (hB (Set.mem_image_of_mem weight hzero))
  exact ⟨B, hB0, fun x hx => hB (Set.mem_image_of_mem weight hx)⟩

/-- A scheduled finite collector using a continuous nonnegative observable
has a square-integrable returned average, uniformly for every starting
point. -/
theorem memLp_scheduledBalancedTransitionCollect_average_of_continuous
    (q : VolumeParams) (I : VolumeInput q.n)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {weight : AmbientSpace q.n → ℝ} (hweight : Continuous weight)
    (hweight0 : ∀ x, 0 ≤ weight x)
    (proposalCap properStride retryLimit samples : ℕ)
    (hsamples : 0 < samples) (current : AmbientSpace q.n) :
    MemLp scheduledBalancedPhaseRatio 2
      ((scheduledBalancedTransitionCollectLaw q I sigma2 weight proposalCap
        properStride retryLimit samples 0 current).map
          (balancedCoolingAverage samples)) := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_scheduledPhaseBody_weight_upper_bound q I hsigma2 hweight hweight0
  apply memLp_scheduledBalancedTransitionCollect_average q I hsigma2
    hweight.measurable hweight0 proposalCap properStride retryLimit samples
    hsamples current hB0
  intro state
  filter_upwards [scheduledBalancedAccuracyTransitionLawAux_ae_mem_phaseBody
    q I hsigma2 proposalCap properStride retryLimit state] with result hresult
  cases result with
  | none => trivial
  | some target => exact hB target hresult

/-- Every executable scheduled Gaussian-ratio phase has an `L²` average. -/
theorem memLp_scheduledBalancedCoolingRatioTransitionLaw_ratio
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (tau2 : ℝ) (current : AmbientSpace q.n) :
    MemLp scheduledBalancedPhaseRatio 2
      (scheduledBalancedCoolingRatioTransitionLaw parameters q I sigma2 tau2
        current) := by
  have hcontinuous : Continuous
      (gaussianRatioWeight (n := q.n) sigma2 tau2) := by
    unfold gaussianRatioWeight
    refine (by fun_prop : Continuous fun x : AmbientSpace q.n =>
      Real.exp (-‖x‖ ^ 2 / (2 * tau2))).div₀ (by fun_prop) ?_
    intro x
    exact Real.exp_ne_zero _
  have hsamples : 0 < figureOnePhaseSampleCount q sigma2 := by
    unfold figureOnePhaseSampleCount
    split_ifs
    · exact figureOneFixedSampleCount_pos q
    · exact figureOneSampleCount_pos q
  simpa [scheduledBalancedCoolingRatioTransitionLaw] using
    memLp_scheduledBalancedTransitionCollect_average_of_continuous
      q I hsigma2 hcontinuous
      (gaussianRatioWeight_nonnegative sigma2 tau2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOnePhaseSampleCount q sigma2)
      hsamples
      (accuracyScaleFactor q • current)

/-- Every executable scheduled terminal Gaussian-to-uniform phase has an
`L²` average. -/
theorem memLp_scheduledBalancedCoolingUniformTransitionLaw_ratio
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (current : AmbientSpace q.n) :
    MemLp scheduledBalancedPhaseRatio 2
      (scheduledBalancedCoolingUniformTransitionLaw parameters q I sigma2
        current) := by
  have hcontinuous : Continuous
      (uniformRatioWeight (n := q.n) sigma2) := by
    unfold uniformRatioWeight
    fun_prop
  simpa [scheduledBalancedCoolingUniformTransitionLaw] using
    memLp_scheduledBalancedTransitionCollect_average_of_continuous
      q I hsigma2 hcontinuous (uniformRatioWeight_nonnegative sigma2)
      (parameters.proposalCap q sigma2)
      (parameters.properStride q sigma2)
      (parameters.retryLimit q sigma2)
      (figureOneSampleCount q) (figureOneSampleCount_pos q)
      (accuracyScaleFactor q • current)

#print axioms exists_scheduledPhaseBody_weight_upper_bound
#print axioms memLp_scheduledBalancedTransitionCollect_average_of_continuous
#print axioms memLp_scheduledBalancedCoolingRatioTransitionLaw_ratio
#print axioms memLp_scheduledBalancedCoolingUniformTransitionLaw_ratio

end ArlibCommunity.Algorithms.CV18
