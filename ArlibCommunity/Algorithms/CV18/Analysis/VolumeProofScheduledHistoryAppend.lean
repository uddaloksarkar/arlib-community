/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license, as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledExecutableFullHistory

/-! # Prefix algebra for scheduled chronological histories -/

namespace ArlibCommunity.Algorithms.CV18

open MeasureTheory ProbabilityTheory

/-- Concatenate a completed tail history after an already accumulated prefix. -/
noncomputable def balancedCoolingHistoryConcat
    (head tail : BalancedCoolingHistory n) : BalancedCoolingHistory n :=
  ((fun k => if k < head.2.1 then head.1 k
      else if k < head.2.1 + tail.2.1 then tail.1 (k - head.2.1)
      else head.1 k),
    head.2.1 + tail.2.1,
    head.2.2.1 * tail.2.2.1,
    tail.2.2.2)

theorem balancedCoolingHistoryConcat_initial
    (head : BalancedCoolingHistory n) :
    balancedCoolingHistoryConcat head
        ((fun _ => 0), 0, 1, head.2.2.2) = head := by
  rcases head with ⟨ratios, count, product, point⟩
  unfold balancedCoolingHistoryConcat
  simp only [Nat.add_zero, mul_one]
  congr 1
  funext k
  by_cases hk : k < count
  · simp [hk]
  · simp [hk]

theorem measurable_balancedCoolingHistoryConcat_left
    (head : BalancedCoolingHistory n) :
    Measurable (balancedCoolingHistoryConcat head) := by
  unfold balancedCoolingHistoryConcat
  apply Measurable.prodMk
  · refine measurable_pi_lambda _ fun k => ?_
    by_cases hk : k < head.2.1
    · simp only [hk, if_true]
      exact measurable_const
    · simp only [hk, if_false]
      apply Measurable.ite
      · exact measurableSet_lt measurable_const
          (measurable_const.add (measurable_fst.comp measurable_snd))
      · exact (measurable_pi_apply (k - head.2.1)).comp measurable_fst
      · exact measurable_const
  · fun_prop

noncomputable def balancedCoolingHistoryConcatOption
    (head : BalancedCoolingHistory n) :
    Option (BalancedCoolingHistory n) → Option (BalancedCoolingHistory n)
  | none => none
  | some tail => some (balancedCoolingHistoryConcat head tail)

theorem measurable_balancedCoolingHistoryConcatOption
    (head : BalancedCoolingHistory n) :
    Measurable (balancedCoolingHistoryConcatOption head) := by
  have hsome : Measurable fun tail : BalancedCoolingHistory n =>
      some (balancedCoolingHistoryConcat head tail) :=
    measurable_some.comp (measurable_balancedCoolingHistoryConcat_left head)
  convert Measurable.optionElim (none : Option (BalancedCoolingHistory n)) hsome using 1
  funext tail
  cases tail <;> rfl

theorem balancedCoolingHistoryConcatOption_initial
    (head : BalancedCoolingHistory n) :
    balancedCoolingHistoryConcatOption head
        (some ((fun _ => 0), 0, 1, head.2.2.2)) = some head := by
  simp only [balancedCoolingHistoryConcatOption]
  rw [balancedCoolingHistoryConcat_initial]

theorem balancedCoolingHistoryConcat_snoc_cons
    (head tail : BalancedCoolingHistory n) (ratio : ℝ)
    (nextPoint : AmbientSpace n) :
    balancedCoolingHistoryConcat head
        ((fun k => if k = 0 then ratio else tail.1 (k - 1)),
          tail.2.1 + 1, ratio * tail.2.2.1, tail.2.2.2) =
      balancedCoolingHistoryConcat
        ((fun k => if k = head.2.1 then ratio else head.1 k),
          head.2.1 + 1, head.2.2.1 * ratio, nextPoint) tail := by
  rcases head with ⟨prefixRatios, prefixCount, prefixProduct, prefixPoint⟩
  rcases tail with ⟨tailRatios, tailCount, tailProduct, tailPoint⟩
  unfold balancedCoolingHistoryConcat
  simp only
  congr 1
  · funext k
    by_cases hk : k < prefixCount
    · have hlt : k < prefixCount + (tailCount + 1) := by omega
      have hlt' : k < prefixCount + 1 := by omega
      have hne : k ≠ prefixCount := by omega
      simp [hk, hlt, hlt', hne]
    · have hkp : prefixCount ≤ k := Nat.le_of_not_gt hk
      by_cases heq : k = prefixCount
      · subst k
        simp
      · have hsucc : prefixCount + 1 ≤ k := by omega
        have hnot : ¬ k < prefixCount + 1 := Nat.not_lt_of_ge hsucc
        have hsubpos : k - prefixCount ≠ 0 := by omega
        have hsub : k - (prefixCount + 1) = k - prefixCount - 1 := by omega
        by_cases htail : k < prefixCount + (tailCount + 1)
        · have htail' : k < prefixCount + 1 + tailCount := by omega
          simp [hk, htail, hnot, hsubpos, hsub, htail']
        · have htail' : ¬ k < prefixCount + 1 + tailCount := by omega
          simp [hk, htail, hnot, htail', heq]
  · ring

/-- The recursive executable law, viewed after an already accumulated
chronological prefix.  This is the bridge between front-cons recursion and
the forward snoc interpreter. -/
noncomputable def scheduledExecutableCoolingHistoryFrom
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (variances : List ℝ)
    (head : BalancedCoolingHistory q.n) :
    Measure (Option (BalancedCoolingHistory q.n)) :=
  (scheduledExecutableCoolingHistoryLaw parameters q I variances head.2.2.2).map
    (balancedCoolingHistoryConcatOption head)

theorem scheduledExecutableCoolingHistoryFrom_nil
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (head : BalancedCoolingHistory q.n) :
    scheduledExecutableCoolingHistoryFrom parameters q I [] head =
      Measure.dirac (some head) := by
  unfold scheduledExecutableCoolingHistoryFrom
  rw [scheduledExecutableCoolingHistoryLaw, Measure.map_dirac'
    (measurable_balancedCoolingHistoryConcatOption head)]
  rw [balancedCoolingHistoryConcatOption_initial]

theorem scheduledExecutableCoolingHistoryFrom_singleton
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 : ℝ)
    (head : BalancedCoolingHistory q.n) :
    scheduledExecutableCoolingHistoryFrom parameters q I [sigma2] head =
      Measure.dirac (some head) := by
  unfold scheduledExecutableCoolingHistoryFrom
  rw [scheduledExecutableCoolingHistoryLaw, Measure.map_dirac'
    (measurable_balancedCoolingHistoryConcatOption head)]
  rw [balancedCoolingHistoryConcatOption_initial]

theorem scheduledExecutableCoolingHistoryFrom_cons_cons
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (sigma2 tau2 : ℝ) (rest : List ℝ)
    (hsigma2 : 0 < sigma2)
    (htailPositive : ∀ s ∈ tau2 :: rest, 0 < s)
    (head : BalancedCoolingHistory q.n) :
    scheduledExecutableCoolingHistoryFrom parameters q I
        (sigma2 :: tau2 :: rest) head =
      (scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2
        head.2.2.2).bind fun phase =>
          match phase with
          | none => Measure.dirac none
          | some (ratio, nextPoint) =>
              scheduledExecutableCoolingHistoryFrom parameters q I
                (tau2 :: rest)
                ((fun k => if k = head.2.1 then ratio else head.1 k),
                  head.2.1 + 1, head.2.2.1 * ratio, nextPoint) := by
  have htail := scheduledExecutableCoolingHistoryLaw_measurable_and_probability
    parameters q I (tau2 :: rest) htailPositive
  let oldContinuation : Option (ℝ × AmbientSpace q.n) →
      Measure (Option (BalancedCoolingHistory q.n)) := fun phase =>
    match phase with
    | none => Measure.dirac none
    | some (ratio, nextPoint) =>
        (scheduledExecutableCoolingHistoryLaw parameters q I
          (tau2 :: rest) nextPoint).map (balancedCoolingHistoryCons ratio)
  have holdContinuation : Measurable oldContinuation := by
    have hsome : Measurable fun value : ℝ × AmbientSpace q.n =>
        (scheduledExecutableCoolingHistoryLaw parameters q I
          (tau2 :: rest) value.2).map
            (balancedCoolingHistoryCons value.1) := by
      apply measurable_measure_map_param_variable
        (htail.1.comp measurable_snd) (fun value => htail.2 value.2)
      exact measurable_balancedCoolingHistoryCons.comp <|
        (measurable_fst.comp measurable_fst).prodMk measurable_snd
    convert Measurable.optionElim
      (Measure.dirac (none : Option (BalancedCoolingHistory q.n))) hsome using 1
    funext phase
    cases phase <;> rfl
  unfold scheduledExecutableCoolingHistoryFrom
  rw [scheduledExecutableCoolingHistoryLaw]
  change ((scheduledBalancedCoolingRatioLaw parameters q I sigma2 tau2
    head.2.2.2).bind oldContinuation).map
      (balancedCoolingHistoryConcatOption head) = _
  rw [map_bind_eq_bind_map_of_measurable _ holdContinuation
    (measurable_balancedCoolingHistoryConcatOption head)]
  apply Measure.bind_congr_right
  filter_upwards with phase
  cases phase with
  | none =>
      rw [Measure.map_dirac'
        (measurable_balancedCoolingHistoryConcatOption head)]
      rfl
  | some value =>
      rcases value with ⟨ratio, nextPoint⟩
      have hcons : Measurable (balancedCoolingHistoryCons (n := q.n) ratio) :=
        (measurable_balancedCoolingHistoryCons (n := q.n)).comp
          (measurable_const.prodMk measurable_id)
      rw [Measure.map_map
        (measurable_balancedCoolingHistoryConcatOption head) hcons]
      apply Measure.map_congr
      filter_upwards with tail
      cases tail with
      | none => rfl
      | some tail =>
          simp only [Function.comp_apply, balancedCoolingHistoryCons,
            balancedCoolingHistoryConcatOption]
          exact congrArg some
            (balancedCoolingHistoryConcat_snoc_cons head tail ratio nextPoint)

noncomputable def scheduledVarianceSegment
    (q : VolumeParams) (offset steps : ℕ) : List ℝ :=
  List.ofFn fun i : Fin (steps + 1) => scheduleValue q (offset + i.1)

@[simp] theorem scheduledVarianceSegment_zero
    (q : VolumeParams) (offset : ℕ) :
    scheduledVarianceSegment q offset 0 = [scheduleValue q offset] := by
  simp [scheduledVarianceSegment]

theorem scheduledVarianceSegment_succ
    (q : VolumeParams) (offset steps : ℕ) :
    scheduledVarianceSegment q offset (steps + 1) =
      scheduleValue q offset :: scheduledVarianceSegment q (offset + 1) steps := by
  unfold scheduledVarianceSegment
  rw [List.ofFn_succ]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  congr 1
  simp only [Fin.val_succ]
  omega

theorem scheduledVarianceSegment_eq_cons_head_tail
    (q : VolumeParams) (offset steps : ℕ) :
    scheduledVarianceSegment q offset steps =
      scheduleValue q offset :: (scheduledVarianceSegment q offset steps).tail := by
  cases steps with
  | zero => simp
  | succ steps =>
      rw [scheduledVarianceSegment_succ]
      simp only [List.tail_cons]

/-- Front-recursive form of the scheduled chronological Gaussian phase law. -/
noncomputable def scheduledExecutableFrontHistoryLaw
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) :
    ℕ → ℕ → Option (BalancedCoolingHistory q.n) →
      Measure (Option (BalancedCoolingHistory q.n))
  | _, 0, history => Measure.dirac history
  | offset, steps + 1, history =>
      match history with
      | none => Measure.dirac none
      | some head =>
          (scheduledBalancedCoolingRatioLaw parameters q I
            (scheduleValue q offset) (scheduleValue q (offset + 1))
            head.2.2.2).bind fun phase =>
              match phase with
              | none => Measure.dirac none
              | some (ratio, nextPoint) =>
                  scheduledExecutableFrontHistoryLaw parameters q I
                    (offset + 1) steps
                    (some ((fun k => if k = head.2.1 then ratio else head.1 k),
                      head.2.1 + 1, head.2.2.1 * ratio, nextPoint))

theorem scheduledExecutableCoolingHistoryFrom_segment_eq_front
    (parameters : BalancedCoolingParameters) (q : VolumeParams)
    (I : VolumeInput q.n) (offset : ℕ) :
    ∀ steps (head : BalancedCoolingHistory q.n),
      scheduledExecutableCoolingHistoryFrom parameters q I
          (scheduledVarianceSegment q offset steps) head =
        scheduledExecutableFrontHistoryLaw parameters q I offset steps
          (some head) := by
  intro steps
  induction steps generalizing offset with
  | zero =>
      intro head
      rw [scheduledVarianceSegment_zero,
        scheduledExecutableCoolingHistoryFrom_singleton]
      rfl
  | succ steps ih =>
      intro head
      rw [scheduledVarianceSegment_succ]
      rw [scheduledVarianceSegment_eq_cons_head_tail q (offset + 1) steps]
      rw [scheduledExecutableCoolingHistoryFrom_cons_cons parameters q I
        (scheduleValue q offset) (scheduleValue q (offset + 1))
        (scheduledVarianceSegment q (offset + 1) steps).tail
        (scheduleValue_pos q offset)]
      · rw [scheduledExecutableFrontHistoryLaw]
        apply Measure.bind_congr_right
        filter_upwards with phase
        cases phase with
        | none => rfl
        | some value =>
            rcases value with ⟨ratio, nextPoint⟩
            simpa only [← scheduledVarianceSegment_eq_cons_head_tail] using
              ih (offset + 1)
                ((fun k => if k = head.2.1 then ratio else head.1 k),
                  head.2.1 + 1, head.2.2.1 * ratio, nextPoint)
      · intro s hs
        rw [show scheduleValue q (offset + 1) ::
            (scheduledVarianceSegment q (offset + 1) steps).tail =
            scheduledVarianceSegment q (offset + 1) steps by
          cases steps with
          | zero => simp
          | succ steps =>
              rw [scheduledVarianceSegment_succ]
              rfl] at hs
        rw [scheduledVarianceSegment, List.mem_ofFn'] at hs
        obtain ⟨i, rfl⟩ := hs
        exact scheduleValue_pos q _

#print axioms balancedCoolingHistoryConcat_initial
#print axioms measurable_balancedCoolingHistoryConcatOption
#print axioms balancedCoolingHistoryConcat_snoc_cons
#print axioms scheduledExecutableCoolingHistoryFrom_cons_cons
#print axioms scheduledExecutableCoolingHistoryFrom_segment_eq_front

end ArlibCommunity.Algorithms.CV18
