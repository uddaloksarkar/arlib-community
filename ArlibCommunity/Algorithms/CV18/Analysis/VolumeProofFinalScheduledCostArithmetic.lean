/- Copyright (c) 2026. All rights reserved. Released under Apache 2.0. -/
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofFinalScheduledParameters
import ArlibCommunity.Algorithms.CV18.Analysis.VolumeProofScheduledRetryShadowDomination

/-! # Arithmetic envelopes for the final scheduled expected-cost proof -/

namespace ArlibCommunity.Algorithms.CV18

open scoped ENNReal BigOperators

/-- The safe finite retry horizon is controlled by the same protected
logarithm that appears in the corrected scheduled mixing stride. -/
theorem figureOneSafeRetryCount_cast_le_correctedMixingLog
    (q : VolumeParams) :
    (figureOneSafeRetryCount q : ℝ) ≤
      129 * protectedLog
        (1 / figureOneCorrectedBlockMixingError q
          (figureOneSafeRetryCount q - 1)) := by
  let nu := figureOnePerSampleMixingError q
  let N := figureOneSafeRetryCount q
  let B := protectedLog
    (1 / figureOneCorrectedBlockMixingError q (N - 1))
  have hnu : 0 < nu := by
    simpa [nu] using figureOnePerSampleMixingError_pos q
  have hNpos : 0 < N := by
    simpa [N] using figureOneSafeRetryCount_pos q
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hrawNonneg : 0 ≤ 128 * protectedLog (4 / nu) := by
    have : 1 ≤ protectedLog (4 / nu) := le_max_left _ _
    positivity
  have hceil : (N : ℝ) < 128 * protectedLog (4 / nu) + 1 := by
    simpa [N, figureOneSafeRetryCount, nu] using
      Nat.ceil_lt_add_one hrawNonneg
  have harg : 4 / nu ≤
      1 / figureOneCorrectedBlockMixingError q (N - 1) := by
    unfold figureOneCorrectedBlockMixingError
    change 4 / nu ≤ 1 / (nu / (4 * (((N - 1 : ℕ) : ℝ) + 1)))
    have hNcast : (((N - 1 : ℕ) : ℝ) + 1) = N := by
      exact_mod_cast Nat.sub_add_cancel hNpos
    rw [hNcast]
    rw [one_div_div]
    apply (div_le_div_iff_of_pos_right hnu).2
    nlinarith
  have hargPos : 0 < 4 / nu := by positivity
  have hprotected : protectedLog (4 / nu) ≤ B := by
    dsimp only [B, protectedLog]
    apply max_le_max_left
    exact Real.strictMonoOn_log.monotoneOn hargPos
      (hargPos.trans_le harg) harg
  have hBone : 1 ≤ B := by
    dsimp only [B, protectedLog]
    exact le_max_left _ _
  dsimp only [N, B, nu] at hceil hprotected hBone ⊢
  nlinarith

#print axioms figureOneSafeRetryCount_cast_le_correctedMixingLog

end ArlibCommunity.Algorithms.CV18
