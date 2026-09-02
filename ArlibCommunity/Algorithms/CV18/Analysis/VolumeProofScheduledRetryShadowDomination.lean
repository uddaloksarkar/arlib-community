/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofKilledChainCost

/-! # Domination of finite scheduled retries by a fixed-trial shadow -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Number of live trials still possible in the lexicographic retry state. -/
def balancedRemainingTrials (retryLimit attempts samples : ℕ) : ℕ :=
  match samples with
  | 0 => 0
  | future + 1 => future * retryLimit + attempts

@[simp] theorem balancedRemainingTrials_zero
    (retryLimit attempts : ℕ) :
    balancedRemainingTrials retryLimit attempts 0 = 0 := rfl

@[simp] theorem balancedRemainingTrials_succ
    (retryLimit attempts future : ℕ) :
    balancedRemainingTrials retryLimit attempts (future + 1) =
      future * retryLimit + attempts := rfl

theorem balancedRemainingTrials_accept
    (retryLimit attempts future : ℕ) :
    balancedRemainingTrials retryLimit retryLimit future ≤
      balancedRemainingTrials retryLimit (attempts + 1) (future + 1) - 1 := by
  cases future with
  | zero => simp [balancedRemainingTrials]
  | succ future =>
      simp only [balancedRemainingTrials, Nat.succ_mul]
      omega

theorem balancedRemainingTrials_reject
    (retryLimit attempts future : ℕ) :
    balancedRemainingTrials retryLimit attempts (future + 1) =
      balancedRemainingTrials retryLimit (attempts + 1) (future + 1) - 1 := by
  simp [balancedRemainingTrials]

/-- Monotonicity of the numerical fixed-chain shadow in its horizon. -/
theorem finiteKilledChainExpectedCost_mono
    {S : Type*} [MeasurableSpace S]
    (next : S → Measure S) (trialCost : S → ENNReal) :
    Monotone fun trials => finiteKilledChainExpectedCost next trialCost trials := by
  intro first second hle
  intro current
  induction second generalizing first current with
  | zero =>
      have : first = 0 := Nat.eq_zero_of_le_zero hle
      subst first
      exact le_rfl
  | succ second ih =>
      cases first with
      | zero => exact bot_le
      | succ first =>
          simp only [finiteKilledChainExpectedCost]
          exact add_le_add le_rfl (lintegral_mono fun state =>
            ih (Nat.le_of_succ_le_succ hle) state)

/-- Integrating over successful endpoints is the same as integrating the
endpoint payload on successful optional outputs and zero on failure. -/
theorem lintegral_successfulEndpointLaw
    {S : Type*} [MeasurableSpace S]
    (law : Measure (Option (ℝ × S)))
    {f : S → ENNReal} (hf : Measurable f) :
    ∫⁻ state, f state ∂successfulEndpointLaw law =
      ∫⁻ output, match output with
        | none => 0
        | some value => f value.2 ∂law := by
  unfold successfulEndpointLaw
  rw [Measure.lintegral_bind measurable_successfulEndpointKernel.aemeasurable
    hf.aemeasurable]
  apply lintegral_congr
  intro output
  cases output with
  | none => simp [successfulEndpointKernel]
  | some value =>
      simp only [successfulEndpointKernel]
      rw [lintegral_dirac' _ hf]

/-- One executable scheduled retry step is bounded by its padded block cost
plus the successful-endpoint average of any uniform continuation envelope. -/
theorem scheduledRetryStep_countedQueryCost_le_padded
    {Result : Type} [MeasurableSpace Result]
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ)
    (current : AmbientSpace q.n)
    (failure : Result)
    (next : AmbientSpace q.n × (Bool × AmbientSpace q.n) →
      MembershipOracleProgram q.n Result)
    (hnext : ∀ z, (next z).CountedStronglyMeasurable oracle.query)
    (hnextRun : Measurable fun z => (next z).run oracle.query)
    (envelope : AmbientSpace q.n → ENNReal)
    (henvelope : Measurable envelope)
    (hbound : ∀ mixed result,
      countedQueryCost ((next (mixed, result)).run oracle.query) ≤
        envelope mixed) :
    countedQueryCost
        (((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
          properStride current).bind fun block =>
            match block with
            | none => .pure failure
            | some (_, mixed) =>
                (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
                  mixed).bind fun result => next (mixed, result)).run
          oracle.query) ≤
      scheduledPaddedTrialCost q I oracle sigma2 proposalCap properStride
        current +
        ∫⁻ state, envelope state ∂scheduledSuccessfulBlockEndpointLaw q I
          sigma2 proposalCap properStride current := by
  let block := cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
    properStride current
  let tail : Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n Result
    | none => .pure failure
    | some (_, mixed) =>
        (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 mixed).bind
          fun result => next (mixed, result)
  have hblock := (cappedScheduledAccuracyProperBlock_countedMeasurable
    q I oracle hsigma2 (proposalCap + 1) properStride).2 current
  have htail : ∀ value, (tail value).CountedStronglyMeasurable oracle.query := by
    intro value
    cases value with
    | none => trivial
    | some value =>
        rcases value with ⟨ignored, mixed⟩
        exact (scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
          q I oracle sigma2 mixed).bind (fun result => hnext (mixed, result))
            (hnextRun.comp (measurable_const.prodMk measurable_id))
  have htailRun : Measurable fun value => (tail value).run oracle.query := by
    have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
        (tail (some value)).run oracle.query := by
      let rejection (value : ℝ × AmbientSpace q.n) :=
        scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 value.2
      let continuation (z : (ℝ × AmbientSpace q.n) ×
          (Bool × AmbientSpace q.n)) := next (z.1.2, z.2)
      apply MembershipOracleProgram.measurable_run_bind_param oracle.query
        rejection continuation
      · apply MembershipOracleProgram.measurable_run_of_fixedQueryCount
          oracle.query rejection 1
        · intro value
          exact scheduledBalancedAccuracyGaussianRejectionAttempt_fixedQueryCount
            q sigma2 value.2
        · intro value
          exact scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
            q I oracle sigma2 value.2
        · rw [show (fun value => (rejection value).runEstimate oracle.query) =
              fun value => scheduledBalancedAccuracyGaussianRejectionKernel
                q I sigma2 value.2 by
              funext value
              exact runEstimate_scheduledBalancedAccuracyGaussianRejectionAttempt
                q I oracle hsigma2 value.2]
          exact (scheduledBalancedAccuracyGaussianRejectionKernel q I sigma2).measurable.comp
            measurable_snd
      · intro value
        exact scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
          q I oracle sigma2 value.2
      · exact hnextRun.comp <|
          (measurable_snd.comp measurable_fst).prodMk measurable_snd
      · intro z
        exact hnext (z.1.2, z.2)
    convert Measurable.optionElim
      (Measure.dirac (failure, 0)) hsome using 1
    funext value
    cases value <;> rfl
  rw [MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query block tail
    hblock htail htailRun]
  unfold scheduledPaddedTrialCost
  let law := block.runEstimate oracle.query
  have hlaw : law = scheduledBalancedAccuracyRetryBlockKernel q I sigma2
      proposalCap properStride current := by
    exact cappedScheduledAccuracyProperBlock_semantics q I oracle hsigma2
      proposalCap properStride current
  let payload : Option (ℝ × AmbientSpace q.n) → ENNReal
    | none => 0
    | some value => envelope value.2
  have hpayload : Measurable payload := by
    convert Measurable.optionElim 0 (henvelope.comp measurable_snd) using 1
    funext value
    cases value <;> rfl
  have htailCost : ∀ value,
      countedQueryCost ((tail value).run oracle.query) ≤ 1 + payload value := by
    intro value
    cases value with
    | none =>
        dsimp only [tail, payload]
        calc
          countedQueryCost
              ((MembershipOracleProgram.pure (n := q.n) failure).run
                oracle.query) ≤ 0 :=
            by simpa only [countedQueryCost, Nat.cast_zero] using
              (MembershipOracleProgram.QueryBound.pure failure 0).lintegral_queryCount_le
                (oracle := oracle.query) (by trivial)
          _ ≤ 1 + 0 := bot_le
    | some value =>
        rcases value with ⟨ignored, mixed⟩
        dsimp only [tail, payload]
        rw [MembershipOracleProgram.countedQueryCost_bind_eq_add oracle.query
          (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 mixed)
          (fun result => next (mixed, result))
          (scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
            q I oracle sigma2 mixed)
          (fun result => hnext (mixed, result))
          (hnextRun.comp (measurable_const.prodMk measurable_id))]
        have hrejectionCost : countedQueryCost
            ((scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
              mixed).run oracle.query) ≤ 1 :=
          by simpa only [countedQueryCost, Nat.cast_one] using
            (scheduledBalancedAccuracyGaussianRejectionAttempt_queryBound
              q sigma2 mixed).lintegral_queryCount_le
                (scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
                  q I oracle sigma2 mixed)
        apply add_le_add hrejectionCost
        let _ : IsProbabilityMeasure
            ((scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
              mixed).runEstimate oracle.query) :=
          MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query _
            (scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
              q I oracle sigma2 mixed).estimateMeasurable
        calc
          (∫⁻ result, countedQueryCost ((next (mixed, result)).run oracle.query)
              ∂(scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
                mixed).runEstimate oracle.query) ≤
              ∫⁻ _result, envelope mixed
                ∂(scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
                  mixed).runEstimate oracle.query := lintegral_mono (hbound mixed)
          _ = envelope mixed := by simp
  have htailIntegral :
      (∫⁻ value, countedQueryCost ((tail value).run oracle.query) ∂law) ≤
        1 + ∫⁻ state, envelope state
          ∂scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
            properStride current := by
    calc
      (∫⁻ value, countedQueryCost ((tail value).run oracle.query) ∂law) ≤
        ∫⁻ value, (1 + payload value) ∂law := lintegral_mono htailCost
      _ = 1 + ∫⁻ value, payload value ∂law := by
        rw [lintegral_add_left measurable_const]
        let _ : IsProbabilityMeasure law :=
          MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle.query block
            hblock.stronglyMeasurable.estimateMeasurable
        simp
      _ = 1 + ∫⁻ state, envelope state
          ∂scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
            properStride current := by
        rw [hlaw]
        congr 1
        change
          (∫⁻ output, match output with
            | none => 0
            | some value => envelope value.2
            ∂scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
              properStride current) =
          ∫⁻ state, envelope state
            ∂successfulEndpointLaw
              (scheduledBalancedAccuracyRetryBlockKernel q I sigma2 proposalCap
                properStride current)
        unfold successfulEndpointLaw
        rw [Measure.lintegral_bind measurable_successfulEndpointKernel.aemeasurable
          henvelope.aemeasurable]
        apply lintegral_congr
        intro output
        cases output with
        | none => simp [successfulEndpointKernel]
        | some value =>
            simp only [successfulEndpointKernel]
            rw [lintegral_dirac' _ henvelope]
  calc
    countedQueryCost (block.run oracle.query) +
        ∫⁻ value, countedQueryCost ((tail value).run oracle.query) ∂law ≤
      countedQueryCost (block.run oracle.query) +
        (1 + ∫⁻ state, envelope state
          ∂scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
            properStride current) := add_le_add le_rfl htailIntegral
    _ = (countedQueryCost (block.run oracle.query) + 1) +
        ∫⁻ state, envelope state
          ∂scheduledSuccessfulBlockEndpointLaw q I sigma2 proposalCap
            properStride current := by ring



end ArlibCommunity.Algorithms.CV18
