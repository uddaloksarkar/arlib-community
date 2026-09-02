/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledCappedDominance
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryCounted
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofExpectedQueryCostBounds

/-! # Cap-independent cost of one scheduled retry trial -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open _root_.Arlib.MarkovChains

/-- One live retry trial: run one proper block and, on success, its balanced
rejection test.  The retained point is the pre-scaling mixed point used by
the executable retry recursion. -/
noncomputable def scheduledBalancedAccuracyLiveTrial
    (q : VolumeParams) (sigma2 : ℝ) (proposalCap properStride : ℕ)
    (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (Bool × AmbientSpace q.n)) :=
  (cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
    properStride current).bind fun block =>
      match block with
      | none => .pure none
      | some (_, mixed) =>
          (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 mixed).bind
            fun result => .pure (some (result.1, mixed))

private noncomputable def scheduledBalancedAccuracyRejectionTail
    (q : VolumeParams) (sigma2 : ℝ) :
    Option (ℝ × AmbientSpace q.n) →
      MembershipOracleProgram q.n (Option (Bool × AmbientSpace q.n))
  | none => .pure none
  | some (_, mixed) =>
      (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 mixed).bind
        fun result => .pure (some (result.1, mixed))

private theorem scheduledBalancedAccuracyRejectionTail_countedMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2) :
    (Measurable fun block =>
      (scheduledBalancedAccuracyRejectionTail q sigma2 block).run oracle.query) ∧
    ∀ block,
      (scheduledBalancedAccuracyRejectionTail q sigma2 block).CountedStronglyMeasurable
        oracle.query := by
  have htail : ∀ block,
      (scheduledBalancedAccuracyRejectionTail q sigma2 block).CountedStronglyMeasurable
        oracle.query := by
    intro block
    cases block with
    | none => trivial
    | some value =>
        rcases value with ⟨ignored, mixed⟩
        apply MembershipOracleProgram.CountedStronglyMeasurable.bind
          (scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
            q I oracle sigma2 mixed) (fun _ => by trivial)
        simp only [MembershipOracleProgram.run]
        exact Measure.measurable_dirac.comp <|
          (measurable_some.comp <| measurable_fst.prodMk measurable_const).prodMk
            measurable_const
  have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
      (scheduledBalancedAccuracyRejectionTail q sigma2 (some value)).run
        oracle.query := by
    apply MembershipOracleProgram.measurable_run_bind_param
      oracle.query
      (fun value : ℝ × AmbientSpace q.n =>
        scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2 value.2)
      (fun z : (ℝ × AmbientSpace q.n) × (Bool × AmbientSpace q.n) =>
        .pure (some (z.2.1, z.1.2)))
    · apply MembershipOracleProgram.measurable_run_of_fixedQueryCount
        oracle.query _ 1
      · intro value
        exact scheduledBalancedAccuracyGaussianRejectionAttempt_fixedQueryCount
          q sigma2 value.2
      · intro value
        exact scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
          q I oracle sigma2 value.2
      · rw [show (fun value : ℝ × AmbientSpace q.n =>
              (scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
                value.2).runEstimate oracle.query) =
            fun value => scheduledBalancedAccuracyGaussianRejectionKernel
              q I sigma2 value.2 by
            funext value
            exact runEstimate_scheduledBalancedAccuracyGaussianRejectionAttempt
              q I oracle hsigma2 value.2]
        exact (scheduledBalancedAccuracyGaussianRejectionKernel
          q I sigma2).measurable.comp measurable_snd
    · intro value
      exact scheduledBalancedAccuracyGaussianRejectionAttempt_countedStronglyMeasurable
        q I oracle sigma2 value.2
    · simp only [MembershipOracleProgram.run]
      exact Measure.measurable_dirac.comp <|
        (measurable_some.comp <|
          (measurable_fst.comp measurable_snd).prodMk
            (measurable_snd.comp measurable_fst)).prodMk measurable_const
    · intro z
      trivial
  refine ⟨?_, htail⟩
  convert Measurable.optionElim
    (Measure.dirac ((none : Option (Bool × AmbientSpace q.n)), 0)) hsome using 1
  funext block
  cases block <;> rfl

private theorem MembershipOracleProgram.FixedQueryCount.countedQueryCost_eq
    {n : ℕ} {A : Type} [MeasurableSpace A]
    {program : MembershipOracleProgram n A} {count : ℕ}
    (hcount : program.FixedQueryCount count)
    (oracle : AmbientSpace n → Bool)
    (hstrong : program.StronglyMeasurable oracle) :
    countedQueryCost (program.run oracle) = count := by
  rw [hcount.run_eq_map_runEstimate oracle hstrong]
  unfold countedQueryCost
  letI : IsProbabilityMeasure (program.runEstimate oracle) :=
    MembershipOracleProgram.runEstimate_isProbabilityMeasure oracle program
      hstrong.estimateMeasurable
  rw [lintegral_map]
  · simp
  · fun_prop
  · fun_prop

theorem scheduledBalancedAccuracyLiveTrial_countedStronglyMeasurable
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) (current : AmbientSpace q.n) :
    (scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
      current).CountedStronglyMeasurable oracle.query := by
  have htail := scheduledBalancedAccuracyRejectionTail_countedMeasurable
    q I oracle hsigma2
  unfold scheduledBalancedAccuracyLiveTrial
  exact (cappedScheduledAccuracyProperBlock_countedMeasurable
    q I oracle hsigma2 (proposalCap + 1) properStride).2 current |>.bind
      htail.2 htail.1

/-- Pointwise, adding the balanced rejection decision costs at most one query
beyond the cap-independent proper-block cost. -/
theorem scheduledBalancedAccuracyLiveTrial_countedQueryCost_le
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    (proposalCap properStride : ℕ) (current : AmbientSpace q.n) :
    countedQueryCost
        ((scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
          current).run oracle.query) ≤
      countedQueryCost
        ((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
          properStride current).run oracle.query) + 1 := by
  let tail := scheduledBalancedAccuracyRejectionTail q sigma2
  have htail := scheduledBalancedAccuracyRejectionTail_countedMeasurable
    q I oracle hsigma2
  have htailCost : ∀ block,
      countedQueryCost ((tail block).run oracle.query) ≤ 1 := by
    intro block
    cases block with
    | none =>
        rw [show tail none = .pure none by rfl]
        have hfixed :
            (MembershipOracleProgram.pure (n := q.n)
              (none : Option (Bool × AmbientSpace q.n))).FixedQueryCount 0 :=
          MembershipOracleProgram.FixedQueryCount.pure _
        rw [hfixed.countedQueryCost_eq oracle.query (by trivial)]
        norm_num
    | some value =>
        rcases value with ⟨ignored, mixed⟩
        have hfixed : (tail (some (ignored, mixed))).FixedQueryCount 1 := by
          change ((scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
            mixed).bind fun result =>
              .pure (some (result.1, mixed))).FixedQueryCount 1
          simpa using
            (scheduledBalancedAccuracyGaussianRejectionAttempt_fixedQueryCount
              q sigma2 mixed).bind
                (fun result => MembershipOracleProgram.FixedQueryCount.pure
                  (some (result.1, mixed)))
        have hstrong : (tail (some (ignored, mixed))).StronglyMeasurable
            oracle.query := by
          change ((scheduledBalancedAccuracyGaussianRejectionAttempt q sigma2
            mixed).bind fun result =>
              .pure (some (result.1, mixed))).StronglyMeasurable oracle.query
          apply (scheduledBalancedAccuracyGaussianRejectionAttempt_stronglyMeasurable
            q I oracle sigma2 mixed).bind (fun _ => by trivial)
          simp only [MembershipOracleProgram.runEstimate]
          exact Measure.measurable_dirac.comp <|
            measurable_some.comp (measurable_fst.prodMk measurable_const)
        exact le_of_eq (by
          simpa only [Nat.cast_one] using
            hfixed.countedQueryCost_eq oracle.query hstrong)
  unfold scheduledBalancedAccuracyLiveTrial
  change countedQueryCost
      (((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
        properStride current).bind tail).run oracle.query) ≤ _
  exact MembershipOracleProgram.countedQueryCost_bind_le_add oracle.query _ tail
    ((cappedScheduledAccuracyProperBlock_countedMeasurable
      q I oracle hsigma2 (proposalCap + 1) properStride).2 current)
    htail.2 htail.1 1 htailCost

/-- Integrated one-trial cost under an arbitrary warm subprobability law.
Crucially, the bound contains no `proposalCap`. -/
theorem lintegral_scheduledBalancedAccuracyLiveTrial_countedQueryCost_le_of_isWarm
    (q : VolumeParams) (I : VolumeInput q.n) (oracle : MembershipOracle I)
    {sigma2 : ℝ} (hsigma2 : 0 < sigma2)
    {M : ENNReal} {mu : Measure (AmbientSpace q.n)}
    (hwarm : _root_.Arlib.IsWarm M mu
      (ellGaussianProb (figureOneScheduledPhaseBody q I sigma2)
        (figureOneScheduledProposalRadius q sigma2) sigma2))
    (proposalCap properStride : ℕ) :
    ∫⁻ current, countedQueryCost
        ((scheduledBalancedAccuracyLiveTrial q sigma2 proposalCap properStride
          current).run oracle.query) ∂mu ≤
      (properStride : ENNReal) * (M * 2) + 2 * mu Set.univ := by
  calc
    _ ≤ ∫⁻ current, (countedQueryCost
          ((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
            properStride current).run oracle.query) + 1) ∂mu :=
      lintegral_mono fun current =>
        scheduledBalancedAccuracyLiveTrial_countedQueryCost_le
          q I oracle hsigma2 proposalCap properStride current
    _ = (∫⁻ current, countedQueryCost
          ((cappedScheduledAccuracyProperBlock q sigma2 (proposalCap + 1)
            properStride current).run oracle.query) ∂mu) + mu Set.univ := by
      rw [lintegral_add_left]
      · simp
      · exact (Measure.measurable_lintegral
          measurable_countedQueryCost_integrand).comp <|
            (cappedScheduledAccuracyProperBlock_countedMeasurable
              q I oracle hsigma2 (proposalCap + 1) properStride).1
    _ ≤ ((properStride : ENNReal) * (M * 2) + mu Set.univ) +
        mu Set.univ := by
      gcongr
      exact lintegral_cappedScheduledAccuracyProperBlock_countedQueryCost_le_of_isWarm_submeasure
        q I oracle hsigma2 hwarm (proposalCap + 1) properStride
    _ = (properStride : ENNReal) * (M * 2) + 2 * mu Set.univ := by ring

end ArlibCommunity.Algorithms.CV18
