/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LL.Analysis

/-!
# The explicit sums appearing in the Linial–Luria bounds

* `wsum d L c = ∑_{r=1}^{L} (r^{d-1}/L^d) log (1 + c (r/L)^d)`.
* `PsiSTS L n` : the bound obtained for `E[log N_{i,j}]` in the Steiner triple system argument.
* `PsiOF L n` : the bound obtained for `E[log N_{i,j}]` in the 1-factorization argument.

and their asymptotic evaluation (with `L = n`):
`PsiSTS n n ≤ (log n - 2 + O(1/√n)) / 6` and `PsiOF n n ≤ (log n - 2 + O(1/√n)) / 2`.
-/

@[expose] public section

open Finset Real

namespace LinialLuria

/-- `wsum d L c = ∑_{r=1}^{L} (r^{d-1}/L^d) log (1 + c (r/L)^d)`. -/
noncomputable def wsum (d L : ℕ) (c : ℝ) : ℝ :=
  ∑ r ∈ range L, ((r + 1 : ℝ) ^ (d - 1) / (L : ℝ) ^ d) * Real.log (1 + c * ((r + 1 : ℝ) / L) ^ d)

/-- The bound for `E[log N_{i,j}]` in the Steiner triple system case. -/
noncomputable def PsiSTS (L n : ℕ) : ℝ :=
  ∑ r ∈ range L, ((r + 1 : ℝ) ^ 2 / (L : ℝ) ^ 3) * wsum 2 L (((n : ℝ) - 3) * ((r + 1 : ℝ) / L) ^ 3)

/-- The bound for `E[log N_{i,j}]` in the 1-factorization case. -/
noncomputable def PsiOF (L n : ℕ) : ℝ :=
  ∑ r ∈ range L, ((r + 1 : ℝ) / (L : ℝ) ^ 2) * wsum 1 L (((n : ℝ) - 2) * ((r + 1 : ℝ) / L) ^ 2)

lemma wsum_nonneg (d L : ℕ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ wsum d L c := by
  unfold wsum
  apply sum_nonneg
  intro r _
  apply mul_nonneg (by positivity)
  apply Real.log_nonneg
  have : 0 ≤ c * ((r + 1 : ℝ) / L) ^ d := by positivity
  linarith

lemma wsum_mono (d L : ℕ) {c c' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') : wsum d L c ≤ wsum d L c' := by
  unfold wsum
  apply sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h0 : 0 ≤ ((r + 1 : ℝ) / L) ^ d := by positivity
  apply Real.log_le_log (by nlinarith)
  nlinarith

lemma sum_sq_range (L : ℕ) : ∑ r ∈ range L, ((r + 1 : ℝ) ^ 2) =
    (L : ℝ) * (L + 1) * (2 * L + 1) / 6 := by
  induction L with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_id_range (L : ℕ) : ∑ r ∈ range L, ((r + 1 : ℝ)) = (L : ℝ) * (L + 1) / 2 := by
  induction L with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; push_cast; ring

lemma x_bounds (L r : ℕ) (hr : r ∈ range L) : 0 < ((r + 1 : ℝ) / L) ∧ ((r + 1 : ℝ) / L) ≤ 1 := by
  have hrL : r + 1 ≤ L := mem_range.1 hr
  have hL : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hL]; exact_mod_cast hrL

/-- The `√` error term in the outer sum. -/
lemma sqrt_term_le (x s K : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (hK : 0 < K) (k : ℕ) :
    x ^ (k + 1) * Real.sqrt (s ^ 2 / (K * x ^ (2 * k + 1))) ≤ Real.sqrt (s ^ 2 / K) := by
  have h1 : x ^ (k + 1) = Real.sqrt (x ^ (2 * k + 2)) := by
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul', Real.sqrt_sq (by positivity)]
  rw [h1, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have : x ^ (2 * k + 2) * (s ^ 2 / (K * x ^ (2 * k + 1))) = x * (s ^ 2 / K) := by
    field_simp; ring
  rw [this]
  have : 0 ≤ s ^ 2 / K := by positivity
  nlinarith

/-- Evaluation of `PsiSTS`, with `s = (L+1)/L`. -/
lemma PsiSTS_le (L n : ℕ) (hL : 1 ≤ L) (hn : 4 ≤ n) :
    PsiSTS L n ≤ (1 / 6) * ((((L + 1 : ℝ) / L) ^ 5) *
        Real.log (1 + ((n : ℝ) - 3) * ((L + 1 : ℝ) / L) ^ 5) -
      ((L + 1 : ℝ) / L) ^ 5 - ((L + 1 : ℝ) / L) ^ 2 +
      ((L + 1 : ℝ) / L) ^ 2 * Real.sqrt (((L + 1 : ℝ) / L) / ((n : ℝ) - 3)) +
      3 * Real.sqrt (((L + 1 : ℝ) / L) ^ 2 / ((n : ℝ) - 3))) := by
  set s : ℝ := (L + 1 : ℝ) / L with hs
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ hLpos]; linarith
  have hn3 : (0 : ℝ) < (n : ℝ) - 3 := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- per-term bound
  have hterm : ∀ r ∈ range L, ((r + 1 : ℝ) ^ 2 / (L : ℝ) ^ 3) *
      wsum 2 L (((n : ℝ) - 3) * ((r + 1 : ℝ) / L) ^ 3) ≤
      (s ^ 2 / 2) * (((r + 1 : ℝ) ^ (3 - 1) / (L : ℝ) ^ 3) *
        Real.log (1 + (((n : ℝ) - 3) * s ^ 2) * ((r + 1 : ℝ) / L) ^ 3)) -
      (s ^ 2 / 2) * ((r + 1 : ℝ) ^ 2 / (L : ℝ) ^ 3) +
      (1 / 2) * (Real.sqrt (s ^ 2 / ((n : ℝ) - 3)) / L) := by
    intro r hr
    obtain ⟨hx0, hx1⟩ := x_bounds L r hr
    set x : ℝ := (r + 1 : ℝ) / L with hx
    have hc : 0 < ((n : ℝ) - 3) * x ^ 3 := by positivity
    have hw := weighted_log_sum_le 2 L (by norm_num) hL _ hc
    change wsum 2 L _ ≤ _ at hw
    have hwr : (r + 1 : ℝ) ^ 2 / (L : ℝ) ^ 3 = x ^ 2 / L := by
      rw [hx]; field_simp
    have hsq := sqrt_term_le x s ((n : ℝ) - 3) hx0 hx1 hn3 1
    norm_num at hsq
    rw [hwr]
    have hpos : 0 ≤ x ^ 2 / L := by positivity
    have := mul_le_mul_of_nonneg_left hw hpos
    rw [← hs] at this
    refine this.trans ?_
    have h3 : (r + 1 : ℝ) ^ (3 - 1) / (L : ℝ) ^ 3 = x ^ 2 / L := by
      rw [hx]; norm_num; field_simp
    rw [show ((n : ℝ) - 3) * x ^ 3 * s ^ 2 = ((n : ℝ) - 3) * s ^ 2 * x ^ 3 by ring]
    have : x ^ 2 * Real.sqrt (s ^ 2 / (((n : ℝ) - 3) * x ^ 3)) / L ≤
        Real.sqrt (s ^ 2 / ((n : ℝ) - 3)) / L :=
      div_le_div_of_nonneg_right hsq hLpos.le
    have e : x ^ 2 / L * (s ^ 2 / ((2:ℕ):ℝ) * (Real.log (1 + ((n : ℝ) - 3) * s ^ 2 * x ^ 3) - 1) +
        Real.sqrt (s ^ 2 / (((n : ℝ) - 3) * x ^ 3)) / ((2:ℕ):ℝ)) =
        s ^ 2 / 2 * (x ^ 2 / L * Real.log (1 + ((n : ℝ) - 3) * s ^ 2 * x ^ 3)) -
        s ^ 2 / 2 * (x ^ 2 / L) +
        1 / 2 * (x ^ 2 * Real.sqrt (s ^ 2 / (((n : ℝ) - 3) * x ^ 3)) / L) := by
      push_cast; ring
    rw [e]
    linarith
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_const, card_range,
    nsmul_eq_mul] at hsum
  change PsiSTS L n ≤ _ at hsum
  have hw3 := weighted_log_sum_le 3 L (by norm_num) hL (((n : ℝ) - 3) * s ^ 2) (by positivity)
  rw [← hs] at hw3
  have hsq3 : ∑ r ∈ range L, ((r + 1 : ℝ) ^ 2 / (L : ℝ) ^ 3) ≥ 1 / 3 := by
    rw [← sum_div, sum_sq_range, ge_iff_le, div_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hsimp1 : Real.sqrt (s ^ 3 / (((n : ℝ) - 3) * s ^ 2)) = Real.sqrt (s / ((n : ℝ) - 3)) := by
    congr 1; field_simp
  rw [hsimp1] at hw3
  have hL1 : (L : ℝ) * ((1 / 2) * (Real.sqrt (s ^ 2 / ((n : ℝ) - 3)) / L)) =
      (1 / 2) * Real.sqrt (s ^ 2 / ((n : ℝ) - 3)) := by field_simp
  rw [hL1] at hsum
  have hlog : 1 + ((n : ℝ) - 3) * s ^ 2 * s ^ 3 = 1 + ((n : ℝ) - 3) * s ^ 5 := by ring
  rw [hlog] at hw3
  have hs2 : 0 ≤ s ^ 2 / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hw3 hs2
  have hsq_nonneg : 0 ≤ Real.sqrt (s / ((n : ℝ) - 3)) := Real.sqrt_nonneg _
  nlinarith

/-- Evaluation of `PsiOF`, with `s = (L+1)/L`. -/
lemma PsiOF_le (L n : ℕ) (hL : 1 ≤ L) (hn : 3 ≤ n) :
    PsiOF L n ≤ (1 / 2) * ((((L + 1 : ℝ) / L) ^ 3) *
        Real.log (1 + ((n : ℝ) - 2) * ((L + 1 : ℝ) / L) ^ 3) -
      ((L + 1 : ℝ) / L) ^ 3 - ((L + 1 : ℝ) / L) +
      ((L + 1 : ℝ) / L) * Real.sqrt (((L + 1 : ℝ) / L) / ((n : ℝ) - 2)) +
      2 * Real.sqrt (((L + 1 : ℝ) / L) / ((n : ℝ) - 2))) := by
  set s : ℝ := (L + 1 : ℝ) / L with hs
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ hLpos]; linarith
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hterm : ∀ r ∈ range L, ((r + 1 : ℝ) / (L : ℝ) ^ 2) *
      wsum 1 L (((n : ℝ) - 2) * ((r + 1 : ℝ) / L) ^ 2) ≤
      s * (((r + 1 : ℝ) ^ (2 - 1) / (L : ℝ) ^ 2) *
        Real.log (1 + (((n : ℝ) - 2) * s) * ((r + 1 : ℝ) / L) ^ 2)) -
      s * ((r + 1 : ℝ) / (L : ℝ) ^ 2) +
      (Real.sqrt (s / ((n : ℝ) - 2)) / L) := by
    intro r hr
    obtain ⟨hx0, hx1⟩ := x_bounds L r hr
    set x : ℝ := (r + 1 : ℝ) / L with hx
    have hc : 0 < ((n : ℝ) - 2) * x ^ 2 := by positivity
    have hw := weighted_log_sum_le 1 L (by norm_num) hL _ hc
    change wsum 1 L _ ≤ _ at hw
    have hwr : (r + 1 : ℝ) / (L : ℝ) ^ 2 = x / L := by
      rw [hx]; field_simp
    have hsq : x * Real.sqrt (s / (((n : ℝ) - 2) * x ^ 2)) = Real.sqrt (s / ((n : ℝ) - 2)) := by
      rw [show x = Real.sqrt (x ^ 2) from (Real.sqrt_sq hx0.le).symm]
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      rw [Real.sq_sqrt (by positivity)]
      field_simp
    rw [hwr]
    have hpos : 0 ≤ x / L := by positivity
    have := mul_le_mul_of_nonneg_left hw hpos
    rw [← hs] at this
    refine this.trans ?_
    have h3 : (r + 1 : ℝ) ^ (2 - 1) / (L : ℝ) ^ 2 = x / L := by
      rw [hx]; norm_num; field_simp
    rw [show ((n : ℝ) - 2) * x ^ 2 * s ^ 1 = ((n : ℝ) - 2) * s * x ^ 2 by ring]
    have e : x / L * (s ^ 1 / ((1:ℕ):ℝ) * (Real.log (1 + ((n : ℝ) - 2) * s * x ^ 2) - 1) +
        Real.sqrt (s ^ 1 / (((n : ℝ) - 2) * x ^ 2)) / ((1:ℕ):ℝ)) =
        s * (x / L * Real.log (1 + ((n : ℝ) - 2) * s * x ^ 2)) - s * (x / L) +
        (x * Real.sqrt (s / (((n : ℝ) - 2) * x ^ 2))) / L := by
      push_cast; ring_nf
    rw [e, hsq, h3]
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_const, card_range,
    nsmul_eq_mul] at hsum
  change PsiOF L n ≤ _ at hsum
  have hw2 := weighted_log_sum_le 2 L (by norm_num) hL (((n : ℝ) - 2) * s) (by positivity)
  rw [← hs] at hw2
  have hid : ∑ r ∈ range L, ((r + 1 : ℝ) / (L : ℝ) ^ 2) ≥ 1 / 2 := by
    rw [← sum_div, sum_id_range, ge_iff_le, div_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hsimp1 : Real.sqrt (s ^ 2 / (((n : ℝ) - 2) * s)) = Real.sqrt (s / ((n : ℝ) - 2)) := by
    congr 1; field_simp
  rw [hsimp1] at hw2
  have hL1 : (L : ℝ) * (Real.sqrt (s / ((n : ℝ) - 2)) / L) = Real.sqrt (s / ((n : ℝ) - 2)) := by
    field_simp
  rw [hL1] at hsum
  have hlog : 1 + ((n : ℝ) - 2) * s * s ^ 2 = 1 + ((n : ℝ) - 2) * s ^ 3 := by ring
  rw [hlog] at hw2
  have hs0 : 0 ≤ s := by linarith
  have := mul_le_mul_of_nonneg_left hw2 hs0
  have hsq_nonneg : 0 ≤ Real.sqrt (s / ((n : ℝ) - 2)) := Real.sqrt_nonneg _
  nlinarith

lemma key_log_bound (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℝ) / n) ^ 5 * Real.log (1 + n * ((n + 1 : ℝ) / n) ^ 5) ≤
      Real.log n + 1100 / Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set q := Real.sqrt n with hq
  have hq1 : 1 ≤ q := by rw [hq]; exact Real.one_le_sqrt.2 hn1
  have hqq : (n : ℝ) = q ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hs : (n + 1 : ℝ) / n = 1 + 1 / n := by field_simp
  set e : ℝ := 1 / n with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by rw [he, div_le_one (by linarith)]; exact hn1
  have hne : (n : ℝ) * e = 1 := by rw [he]; field_simp
  rw [hs]
  have hs5 : (1 + e) ^ 5 ≤ 1 + 31 * e := by
    have h2 : e ^ 2 ≤ e := by nlinarith
    have h3 : e ^ 3 ≤ e := by nlinarith
    have h4 : e ^ 4 ≤ e := by nlinarith
    have h5 : e ^ 5 ≤ e := by nlinarith
    nlinarith
  have hs50 : 1 ≤ (1 + e) ^ 5 := one_le_pow₀ (by linarith)
  have hlog : Real.log (1 + n * (1 + e) ^ 5) ≤ Real.log n + 32 * e := by
    have h1 : 1 + n * (1 + e) ^ 5 ≤ n * (1 + 32 * e) := by nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by positivity) (by positivity)] at h2
    have h3 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 32 * e by positivity)
    linarith
  have hlogn : Real.log n ≤ 2 * q := by
    rw [hqq, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < q by linarith)
    push_cast; linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog0 : 0 ≤ Real.log (1 + n * (1 + e) ^ 5) := Real.log_nonneg (by nlinarith)
  have hmain : (1 + e) ^ 5 * Real.log (1 + n * (1 + e) ^ 5) ≤
      (1 + 31 * e) * (Real.log n + 32 * e) :=
    mul_le_mul hs5 hlog hlog0 (by positivity)
  have heq : e * q ^ 2 = 1 := by rw [← hqq]; linarith
  have hfin : (1 + 31 * e) * (Real.log n + 32 * e) ≤ Real.log n + 1100 / q := by
    rw [show (1100 : ℝ) / q = 1100 * e * q by
      field_simp; nlinarith]
    have h1 : e * Real.log n ≤ 2 * e * q := by nlinarith
    have h2 : e ≤ e * q := by nlinarith
    have h3 : e * e ≤ e := by nlinarith
    nlinarith
  linarith

/-- With `L = n`: `PsiSTS n n ≤ (log n - 2 + 1200/√(n-3)) / 6`. -/
theorem PsiSTS_asymp (n : ℕ) (hn : 4 ≤ n) :
    PsiSTS n n ≤ (1 / 6) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 3)) := by
  have h := PsiSTS_le n n (by omega) hn
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  set s : ℝ := (n + 1 : ℝ) / n with hs
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ (by linarith)]; linarith
  have hs2 : s ≤ 5 / 4 := by rw [hs, div_le_iff₀ (by linarith)]; linarith
  have hk := key_log_bound n (by omega)
  rw [← hs] at hk
  have hn3 : (0 : ℝ) < n - 3 := by linarith
  set r := Real.sqrt ((n : ℝ) - 3) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hn3
  have hrn : r ≤ Real.sqrt n := Real.sqrt_le_sqrt (by linarith)
  have h1 : s ^ 5 * Real.log (1 + ((n : ℝ) - 3) * s ^ 5) ≤
      s ^ 5 * Real.log (1 + n * s ^ 5) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.log_le_log (by nlinarith [one_le_pow₀ (n := 5) hs1])
    nlinarith [one_le_pow₀ (n := 5) hs1]
  have h2 : 1100 / Real.sqrt n ≤ 1100 / r := div_le_div_of_nonneg_left (by norm_num) hr0 hrn
  have h3 : Real.sqrt (s / ((n : ℝ) - 3)) ≤ s / r := by
    rw [Real.sqrt_div' _ hn3.le, ← hr]
    apply div_le_div_of_nonneg_right _ hr0.le
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h4 : Real.sqrt (s ^ 2 / ((n : ℝ) - 3)) = s / r := by
    rw [Real.sqrt_div' _ hn3.le, Real.sqrt_sq (by linarith)]
  rw [h4] at h
  have h5 : s ^ 2 * Real.sqrt (s / ((n : ℝ) - 3)) ≤ s ^ 2 * (s / r) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h6 : s ^ 2 * (s / r) ≤ 2 / r := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hr0]; nlinarith
  have h7 : 3 * (s / r) ≤ 4 / r := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hr0]; nlinarith
  have h8 : 1200 / r = 1100 / r + 2 / r + 4 / r + 94 / r := by ring
  have h9 : 0 ≤ 94 / r := by positivity
  have h10 : 2 ≤ s ^ 5 + s ^ 2 := by nlinarith [one_le_pow₀ (n := 5) hs1, one_le_pow₀ (n := 2) hs1]
  rw [h8]
  linarith

/-- With `L = n`: `PsiOF n n ≤ (log n - 2 + 1200/√(n-2)) / 2`. -/
theorem PsiOF_asymp (n : ℕ) (hn : 3 ≤ n) :
    PsiOF n n ≤ (1 / 2) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 2)) := by
  have h := PsiOF_le n n (by omega) hn
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set s : ℝ := (n + 1 : ℝ) / n with hs
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ (by linarith)]; linarith
  have hs2 : s ≤ 4 / 3 := by rw [hs, div_le_iff₀ (by linarith)]; linarith
  have hk := key_log_bound n (by omega)
  rw [← hs] at hk
  have hn2 : (0 : ℝ) < n - 2 := by linarith
  set r := Real.sqrt ((n : ℝ) - 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hn2
  have hrn : r ≤ Real.sqrt n := Real.sqrt_le_sqrt (by linarith)
  have hs3 : s ^ 3 ≤ s ^ 5 := pow_le_pow_right₀ hs1 (by norm_num)
  have h1 : s ^ 3 * Real.log (1 + ((n : ℝ) - 2) * s ^ 3) ≤
      s ^ 5 * Real.log (1 + n * s ^ 5) := by
    apply mul_le_mul hs3 _ (Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 3) hs1]))
      (by positivity)
    apply Real.log_le_log (by nlinarith [one_le_pow₀ (n := 3) hs1])
    nlinarith [one_le_pow₀ (n := 3) hs1]
  have h2 : 1100 / Real.sqrt n ≤ 1100 / r := div_le_div_of_nonneg_left (by norm_num) hr0 hrn
  have h3 : Real.sqrt (s / ((n : ℝ) - 2)) ≤ s / r := by
    rw [Real.sqrt_div' _ hn2.le, ← hr]
    apply div_le_div_of_nonneg_right _ hr0.le
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h5 : s * Real.sqrt (s / ((n : ℝ) - 2)) ≤ s * (s / r) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h6 : s * (s / r) ≤ 2 / r := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hr0]; nlinarith
  have h7 : 2 * (s / r) ≤ 3 / r := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hr0]; nlinarith
  have h8 : 1200 / r = 1100 / r + 2 / r + 3 / r + 95 / r := by ring
  have h9 : 0 ≤ 95 / r := by positivity
  have h10 : 2 ≤ s ^ 3 + s := by nlinarith [one_le_pow₀ (n := 3) hs1]
  rw [h8]
  linarith

end LinialLuria
