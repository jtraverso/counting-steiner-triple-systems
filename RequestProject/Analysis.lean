/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Elementary real-analysis estimates used in Section 4

Numerical bounds (`log 3 ≤ 1.1`, `e^{4.5} > 79`, `e^5 > 143`), the inequality `key_ineq` used in
the induction proving (4.3), and the asymptotic inequality `step_ineq` used for Theorem 3.
-/

@[expose] public section

namespace STS

lemma log_three_le : Real.log 3 ≤ 1.1 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.quadratic_le_exp_of_nonneg (x := 0.1) (by norm_num)
  have : Real.exp 1.1 = Real.exp 1 * Real.exp 0.1 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith

lemma exp_four_half_gt : (79 : ℝ) < Real.exp 4.5 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp (0.5 : ℝ)
  have : Real.exp 4.5 = Real.exp 1 ^ 4 * Real.exp 0.5 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [this]
  have h3 : (2.7182818283:ℝ)^4 < Real.exp 1 ^ 4 := by gcongr
  nlinarith

lemma exp_five_gt : (143 : ℝ) < Real.exp 5 := by
  have h1 := Real.exp_one_gt_d9
  have : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h3 : (2.7182818283:ℝ)^5 < Real.exp 1 ^ 5 := by gcongr
  nlinarith

lemma log_le_div_24 (x : ℝ) (hx : 122 ≤ x) : Real.log x ≤ x / 24 := by
  have h1 := Real.log_le_sub_one_of_pos (x := x / 64) (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h1
  have h2 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64:ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

lemma key_ineq (n w : ℝ) (hn : 20 ≤ n) (hw0 : 0 ≤ w) (hw7 : w ≤ 7) :
    (3 * n + w) ^ 2 * (Real.log (3 * n + w) - 4.5) ≤
      6 * n ^ 2 * (Real.log n - 2) + 3 * (n + w) ^ 2 * (Real.log (n + w) - 4.5) := by
  have hn0 : 0 < n := by linarith
  have h1 : Real.log (3 * n + w) ≤ Real.log 3 + Real.log n + w / (3 * n) := by
    have := Real.log_le_sub_one_of_pos (x := (3 * n + w) / (3 * n)) (by positivity)
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hn0.ne'] at this
    have e : (3 * n + w) / (3 * n) - 1 = w / (3 * n) := by field_simp; ring
    linarith
  have h2 : Real.log n ≤ Real.log (n + w) := Real.log_le_log hn0 (by linarith)
  have h3 := log_three_le
  have ha : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  set a := Real.log n
  have hk : (3 * n + w) ^ 2 * (w / (3 * n)) ≤ 3 * n * w + 2 * w ^ 2 + 6 := by
    have e : (3 * n + w) ^ 2 * (w / (3 * n)) = 3 * n * w + 2 * w ^ 2 + w ^ 3 / (3 * n) := by
      field_simp; ring
    rw [e]
    have : w ^ 3 / (3 * n) ≤ 6 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [pow_le_pow_left₀ hw0 hw7 3]
    linarith
  calc (3 * n + w) ^ 2 * (Real.log (3 * n + w) - 4.5)
      ≤ (3 * n + w) ^ 2 * (1.1 + a + w / (3 * n) - 4.5) := by gcongr; linarith
    _ = (3 * n + w) ^ 2 * (a - 3.4) + (3 * n + w) ^ 2 * (w / (3 * n)) := by ring
    _ ≤ 6 * n ^ 2 * (a - 2) + 3 * (n + w) ^ 2 * (a - 4.5) := by
        nlinarith [mul_nonneg (mul_nonneg hw0 hw0) ha, mul_nonneg (sub_nonneg.2 hn) hn0.le,
          mul_nonneg (sub_nonneg.2 hw7) hn0.le, mul_nonneg hw0 (sub_nonneg.2 hw7)]
    _ ≤ _ := by gcongr

lemma step_ineq (c δ : ℝ) (hδ : 0 < δ) : ∃ V0 : ℝ, ∀ v n u : ℝ, V0 ≤ v → (v - 7) / 3 ≤ n →
    v / 3 ≤ u → v ^ 2 * (Real.log v - (Real.log 3 + 4 / 3 + c / 3 + δ)) ≤
      6 * n ^ 2 * (Real.log n - 2) + 3 * u ^ 2 * (Real.log u - c) := by
  have hA := Real.tendsto_log_atTop.eventually_ge_atTop (max (Real.log 3 + c) (Real.log 3 + δ / 2 + 2))
  have hB := (Real.isLittleO_log_id_atTop.bound (c := δ / 14) (by positivity))
  have hC := Filter.eventually_ge_atTop (max 8 (7 + 14 / δ))
  obtain ⟨V0, hV0⟩ := Filter.eventually_atTop.1 (hA.and (hB.and hC))
  refine ⟨V0, fun v n u hv hn hu => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hV0 v hv
  rw [max_le_iff] at hA hC
  have hv8 : 8 ≤ v := hC.1
  have hv0 : 0 < v := by linarith
  have hlv0 : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
  simp only [Real.norm_eq_abs, id, abs_of_nonneg hlv0, abs_of_pos hv0] at hB
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hn0 : 0 < (v - 7) / 3 := by linarith
  -- lower bound for log n
  have hln : Real.log v - Real.log 3 - δ / 2 ≤ Real.log n := by
    have h1 : Real.log ((v - 7) / 3) ≤ Real.log n := Real.log_le_log hn0 hn
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have h2 := Real.log_le_sub_one_of_pos (x := v / (v - 7)) (div_pos hv0 (by linarith))
    rw [Real.log_div (by linarith) (by linarith)] at h2
    have hv7 : v - 7 ≠ 0 := by linarith
    have h3 : v / (v - 7) - 1 = 7 / (v - 7) := by field_simp; ring
    have h4 : 7 / (v - 7) ≤ δ / 2 := by
      rw [div_le_iff₀ (by linarith)]
      have := hC.2
      have : 14 / δ * δ = 14 := by field_simp
      nlinarith
    linarith
  set X := Real.log v - Real.log 3 - δ / 2 - 2 with hX
  have hX0 : 0 ≤ X := by linarith [hA.2]
  have hXl : X ≤ Real.log v := by linarith
  have h6 : 2 / 3 * (v ^ 2 - 14 * v) * X ≤ 6 * n ^ 2 * (Real.log n - 2) := by
    have hnn : ((v - 7) / 3) ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hn0.le hn 2
    have : 6 * n ^ 2 * X ≤ 6 * n ^ 2 * (Real.log n - 2) := by gcongr; linarith
    nlinarith
  have hu0 : 0 < v / 3 := by positivity
  have h3u : 3 * (v / 3) ^ 2 * (Real.log v - Real.log 3 - c) ≤ 3 * u ^ 2 * (Real.log u - c) := by
    have h1 : Real.log (v / 3) ≤ Real.log u := Real.log_le_log hu0 hu
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have : 0 ≤ Real.log v - Real.log 3 - c := by linarith [hA.1]
    have hnn : (v / 3) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hu0.le hu 2
    calc 3 * (v / 3) ^ 2 * (Real.log v - Real.log 3 - c) ≤ 3 * u ^ 2 * (Real.log v - Real.log 3 - c) := by
          gcongr
      _ ≤ _ := by gcongr
  have hvX : 14 * v * X ≤ δ * v ^ 2 := by nlinarith
  nlinarith

end STS
