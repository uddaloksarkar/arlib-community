/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofBalancedRejection
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofAccuracyImportanceLaw

/-!
# Finite executable balanced KLS retries

Each trial first advances a capped block of proper speedy steps, then performs
one balanced KLS rejection test.  Rejection retains the unscaled speedy state
and consumes one retry; acceptance records the transformed target, resets the
retry budget, and begins the next sample.  Exhausting either a proposal cap or
a retry budget returns `none`.
-/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- Parameterized measurable elimination for the local `Option` measurable
space used by membership-oracle programs. -/
theorem Measurable.optionElimParam
    {P A B : Type*} [MeasurableSpace P] [MeasurableSpace A]
    [MeasurableSpace B] {noneValue : P → B} {someValue : P × A → B}
    (hnone : Measurable noneValue) (hsome : Measurable someValue) :
    Measurable fun z : P × Option A =>
      match z.2 with
      | none => noneValue z.1
      | some a => someValue (z.1, a) := by
  let encode : P × Option A → (P × Unit) ⊕ (P × A) := fun z =>
    MeasurableEquiv.prodSumDistrib P Unit A (z.1, optionToSum z.2)
  have hencode : Measurable encode := by
    exact (MeasurableEquiv.prodSumDistrib P Unit A).measurable.comp
      (measurable_fst.prodMk (measurable_optionToSum.comp measurable_snd))
  have hout : Measurable
      (Sum.elim (fun z : P × Unit => noneValue z.1) someValue) :=
    (hnone.comp measurable_fst).sumElim hsome
  convert hout.comp hencode using 1
  funext z
  rcases z with ⟨p, value⟩
  cases value <;> rfl

/-- A finite, globally bounded collector of balanced KLS samples.  The
`attempts` argument is the retry budget remaining for the current sample;
`retryLimit` is restored after every success. -/
noncomputable def balancedAccuracyRetryCollectAux (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    ℕ → ℕ → ℝ → AmbientSpace q.n →
      MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n))
  | _, 0, total, current => .pure (some (total, current))
  | 0, _ + 1, _, _ => .pure none
  | attempts + 1, samples + 1, total, current =>
      (cappedAccuracyProperCollectWeights q sigma2 (fun _ => 0)
        (proposalCap + 1) properStride 1 current).bind fun block =>
        match block with
        | none => .pure none
        | some (_, mixed) =>
            (balancedAccuracyGaussianRejectionAttempt q sigma2 mixed).bind
              fun result =>
                if result.1 then
                  balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit retryLimit samples
                    (total + weight result.2) mixed
                else
                  balancedAccuracyRetryCollectAux q sigma2 weight proposalCap
                    properStride retryLimit attempts (samples + 1) total mixed
termination_by attempts samples total current => (samples, attempts)

noncomputable def balancedAccuracyRetryCollect (q : VolumeParams)
    (sigma2 : ℝ) (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    MembershipOracleProgram q.n (Option (ℝ × AmbientSpace q.n)) :=
  balancedAccuracyRetryCollectAux q sigma2 weight proposalCap properStride
    retryLimit retryLimit samples 0 current

/-- Number of queries reserved for all full future samples and the attempts
remaining for the current sample. -/
def balancedRetryQueryBudget (proposalCap retryLimit attempts samples : ℕ) : ℕ :=
  match samples with
  | 0 => 0
  | future + 1 => (future * retryLimit + attempts) * (proposalCap + 2)

theorem balancedRetryQueryBudget_full
    (proposalCap retryLimit samples : ℕ) :
    balancedRetryQueryBudget proposalCap retryLimit retryLimit samples =
      samples * retryLimit * (proposalCap + 2) := by
  cases samples with
  | zero => simp [balancedRetryQueryBudget]
  | succ samples =>
      simp [balancedRetryQueryBudget, Nat.succ_mul]

theorem balancedRetryQueryBudget_step
    (proposalCap retryLimit attempts future : ℕ) :
    (proposalCap + 2) +
        balancedRetryQueryBudget proposalCap retryLimit attempts (future + 1) =
      balancedRetryQueryBudget proposalCap retryLimit (attempts + 1)
        (future + 1) := by
  simp only [balancedRetryQueryBudget, Nat.add_mul]
  omega

/-- Every trial uses at most `proposalCap + 1` queries for the capped proper
block (including its harmless zero observation) and one query for KLS. -/
theorem balancedAccuracyRetryCollectAux_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit : ℕ) :
    ∀ attempts samples total current,
    (balancedAccuracyRetryCollectAux q sigma2 weight proposalCap properStride
      retryLimit attempts samples total current).QueryBound
        (balancedRetryQueryBudget proposalCap retryLimit attempts samples) := by
  intro attempts samples
  induction samples using Nat.strong_induction_on generalizing attempts with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          intro total current
          rw [balancedAccuracyRetryCollectAux]
          exact .pure _ _
      | succ future =>
          induction attempts with
          | zero =>
              intro total current
              rw [balancedAccuracyRetryCollectAux]
              exact .pure _ _
          | succ attempts ihAttempts =>
              intro total current
              simp only [balancedAccuracyRetryCollectAux]
              let block := cappedAccuracyProperCollectWeights q sigma2
                (fun _ => 0) (proposalCap + 1) properStride 1 current
              let tail : Option (ℝ × AmbientSpace q.n) →
                  MembershipOracleProgram q.n
                    (Option (ℝ × AmbientSpace q.n)) := fun value =>
                match value with
                | none => .pure none
                | some (_, mixed) =>
                    (balancedAccuracyGaussianRejectionAttempt q sigma2 mixed).bind
                      fun result =>
                        if result.1 then
                          balancedAccuracyRetryCollectAux q sigma2 weight
                            proposalCap properStride retryLimit retryLimit future
                            (total + weight result.2) mixed
                        else
                          balancedAccuracyRetryCollectAux q sigma2 weight
                            proposalCap properStride retryLimit attempts
                            (future + 1) total mixed
              have hblock : block.QueryBound (proposalCap + 1) := by
                dsimp [block]
                exact cappedAccuracyProperCollectWeights_queryBound q sigma2
                  (fun _ => 0) (proposalCap + 1) properStride 1 current
              have htail : ∀ value, (tail value).QueryBound
                  (1 + balancedRetryQueryBudget proposalCap retryLimit attempts
                    (future + 1)) := by
                intro value
                cases value with
                | none => exact .pure _ _
                | some value =>
                    rcases value with ⟨ignored, mixed⟩
                    dsimp only [tail]
                    apply MembershipOracleProgram.QueryBound.bind
                      (balancedAccuracyGaussianRejectionAttempt_queryBound
                        q sigma2 mixed)
                    intro result
                    by_cases hresult : result.1 = true
                    · simp only [hresult, if_true]
                      have hrec := ihSamples future (by omega) retryLimit
                        (total + weight result.2) mixed
                      rw [balancedRetryQueryBudget_full] at hrec
                      exact hrec.mono <| Nat.mul_le_mul_right
                        (proposalCap + 2) (Nat.le_add_right _ attempts)
                    · have hfalse : result.1 = false :=
                        Bool.eq_false_of_not_eq_true hresult
                      simp only [hfalse, Bool.false_eq_true, if_false]
                      exact ihAttempts total mixed
              have hbound := hblock.bind htail
              change (block.bind tail).QueryBound
                (balancedRetryQueryBudget proposalCap retryLimit
                  (attempts + 1) (future + 1))
              rw [← balancedRetryQueryBudget_step]
              have heq : proposalCap + 1 +
                    (1 + balancedRetryQueryBudget proposalCap retryLimit attempts
                      (future + 1)) =
                  proposalCap + 2 +
                    balancedRetryQueryBudget proposalCap retryLimit attempts
                      (future + 1) := by omega
              rw [← heq]
              exact hbound

theorem balancedAccuracyRetryCollect_queryBound
    (q : VolumeParams) (sigma2 : ℝ)
    (weight : AmbientSpace q.n → ℝ)
    (proposalCap properStride retryLimit samples : ℕ)
    (current : AmbientSpace q.n) :
    (balancedAccuracyRetryCollect q sigma2 weight proposalCap properStride
      retryLimit samples current).QueryBound
        (samples * retryLimit * (proposalCap + 2)) :=
  by
    unfold balancedAccuracyRetryCollect
    have h := balancedAccuracyRetryCollectAux_queryBound q sigma2 weight
      proposalCap properStride retryLimit retryLimit samples 0 current
    rwa [balancedRetryQueryBudget_full] at h

/-- Measure-level counterpart of the balanced retry collector.  `B` is one
capped proper-step block and `R` is the balanced KLS kernel. -/
noncomputable def balancedRetryCollectLawAux
    {S : Type*} [MeasurableSpace S]
    (B : Kernel S (Option (ℝ × S))) (R : Kernel S (Bool × S))
    (weight : S → ℝ) (retryLimit : ℕ) :
    ℕ → ℕ → ℝ → S → Measure (Option (ℝ × S))
  | _, 0, total, current => Measure.dirac (some (total, current))
  | 0, _ + 1, _, _ => Measure.dirac none
  | attempts + 1, samples + 1, total, current =>
      (B current).bind fun block =>
        match block with
        | none => Measure.dirac none
        | some (_, mixed) =>
            (R mixed).bind fun result =>
              if result.1 then
                balancedRetryCollectLawAux B R weight retryLimit retryLimit
                  samples (total + weight result.2) mixed
              else
                balancedRetryCollectLawAux B R weight retryLimit attempts
                  (samples + 1) total mixed
termination_by attempts samples total current => (samples, attempts)

theorem balancedRetryCollectLawAux_measurable_and_probability
    {S : Type*} [MeasurableSpace S]
    (B : Kernel S (Option (ℝ × S))) (R : Kernel S (Bool × S))
    [IsMarkovKernel B] [IsMarkovKernel R]
    {weight : S → ℝ} (hweight : Measurable weight) (retryLimit : ℕ) :
    ∀ attempts samples,
      Measurable (fun state : ℝ × S =>
        balancedRetryCollectLawAux B R weight retryLimit attempts samples
          state.1 state.2) ∧
      ∀ total current, IsProbabilityMeasure
        (balancedRetryCollectLawAux B R weight retryLimit attempts samples
          total current) := by
  intro attempts samples
  induction samples using Nat.strong_induction_on generalizing attempts with
  | h samples ihSamples =>
      cases samples with
      | zero =>
          simp only [balancedRetryCollectLawAux]
          constructor
          · exact Measure.measurable_dirac.comp <|
              measurable_some.comp (measurable_fst.prodMk measurable_snd)
          · intro total current
            infer_instance
      | succ future =>
          induction attempts with
          | zero =>
              simp only [balancedRetryCollectLawAux]
              constructor
              · exact Measure.measurable_dirac.comp measurable_const
              · intro total current
                infer_instance
          | succ attempts ihAttempts =>
              let nextResult : ((ℝ × S) × S) × (Bool × S) →
                  Measure (Option (ℝ × S)) := fun value =>
                if value.2.1 then
                  balancedRetryCollectLawAux B R weight retryLimit retryLimit
                    future (value.1.1.1 + weight value.2.2) value.1.2
                else
                  balancedRetryCollectLawAux B R weight retryLimit attempts
                    (future + 1) value.1.1.1 value.1.2
              have hnextResult : Measurable nextResult := by
                dsimp only [nextResult]
                apply Measurable.ite
                · exact (measurable_fst.comp measurable_snd)
                    (measurableSet_singleton true)
                · exact (ihSamples future (by omega) retryLimit).1.comp <|
                    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).add
                      (hweight.comp (measurable_snd.comp measurable_snd))).prodMk
                        (measurable_snd.comp measurable_fst))
                · exact ihAttempts.1.comp <|
                    ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
                      (measurable_snd.comp measurable_fst))
              let someTail : (ℝ × S) × (ℝ × S) →
                  Measure (Option (ℝ × S)) := fun value =>
                (R value.2.2).bind fun result =>
                  nextResult ((value.1, value.2.2), result)
              have hsomeTail : Measurable someTail := by
                dsimp only [someTail]
                exact measurable_measure_bind_param_variable
                  (R.measurable.comp (measurable_snd.comp measurable_snd))
                  (fun value => IsMarkovKernel.isProbabilityMeasure value.2.2)
                  (hnextResult.comp <|
                    (((measurable_fst.comp measurable_fst).prodMk
                      (measurable_snd.comp
                        (measurable_snd.comp measurable_fst))).prodMk
                          measurable_snd))
              let tail : (ℝ × S) × Option (ℝ × S) →
                  Measure (Option (ℝ × S)) := fun value =>
                match value.2 with
                | none => Measure.dirac none
                | some block => someTail (value.1, block)
              have htail : Measurable tail := by
                dsimp only [tail]
                convert Measurable.optionElimParam
                  (noneValue := fun _ : ℝ × S =>
                    Measure.dirac (none : Option (ℝ × S)))
                  (someValue := someTail)
                  (Measure.measurable_dirac.comp measurable_const) hsomeTail using 1
                ext value
                cases value.2 <;> rfl
              have hlaw : (fun state : ℝ × S =>
                    balancedRetryCollectLawAux B R weight retryLimit
                      (attempts + 1) (future + 1) state.1 state.2) =
                  fun state => (B state.2).bind fun block =>
                    tail (state, block) := by
                funext state
                simp only [balancedRetryCollectLawAux]
                apply Measure.bind_congr_right
                filter_upwards with block
                cases block with
                | none => rfl
                | some block =>
                    rcases block with ⟨ignored, mixed⟩
                    dsimp only [tail, someTail]
              constructor
              · rw [hlaw]
                exact measurable_measure_bind_param_variable
                  (B.measurable.comp measurable_snd)
                  (fun state => IsMarkovKernel.isProbabilityMeasure state.2)
                  htail
              · intro total current
                have hlawPoint :
                    balancedRetryCollectLawAux B R weight retryLimit
                        (attempts + 1) (future + 1) total current =
                      (B current).bind fun block =>
                        tail ((total, current), block) := by
                  simp only [balancedRetryCollectLawAux]
                  apply Measure.bind_congr_right
                  filter_upwards with block
                  cases block with
                  | none => rfl
                  | some block =>
                      rcases block with ⟨ignored, mixed⟩
                      dsimp only [tail, someTail]
                rw [hlawPoint]
                apply MeasureTheory.isProbabilityMeasure_bind
                  (htail.comp
                    (measurable_const.prodMk measurable_id)).aemeasurable
                filter_upwards with block
                cases block with
                | none =>
                    change IsProbabilityMeasure
                      (Measure.dirac (none : Option (ℝ × S)))
                    infer_instance
                | some block =>
                    rcases block with ⟨ignored, mixed⟩
                    dsimp only [tail, someTail]
                    apply MeasureTheory.isProbabilityMeasure_bind
                      (hnextResult.comp
                        (measurable_const.prodMk measurable_id)).aemeasurable
                    filter_upwards with result
                    change IsProbabilityMeasure
                      (if result.1 then
                        balancedRetryCollectLawAux B R weight retryLimit
                          retryLimit future (total + weight result.2) mixed
                       else
                        balancedRetryCollectLawAux B R weight retryLimit
                          attempts (future + 1) total mixed)
                    cases hresult : result.1
                    · simpa only [hresult, Bool.false_eq_true, if_false] using
                        ihAttempts.2 total mixed
                    · simpa only [hresult, if_true] using
                        (ihSamples future (by omega) retryLimit).2
                          (total + weight result.2) mixed

end ArlibCommunity.Algorithms.CV18
