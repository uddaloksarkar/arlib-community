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

#print axioms balancedCoolingHistoryConcat_initial
#print axioms balancedCoolingHistoryConcat_snoc_cons

end ArlibCommunity.Algorithms.CV18
