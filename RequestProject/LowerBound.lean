/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Analysis
public import RequestProject.Construction

/-!
# Section 4 of the paper: lower bounds for `N(v)`

* `STS.D7_lower` : inequality (4.3), `log D₇(v) ≥ (α/6) v² (log v - 4.5)`.
* `STS.lowerBound_of_latin` : the implication (4.1) ⇒ (4.2).
* `STS.theorem2`, `STS.theorem2_vdW` : Theorem 2.
* `STS.theorem3`, `STS.theorem3_vdW` : Theorem 3.
-/

@[expose] public section

open Finset Filter

namespace STS

lemma log_mul_pow_le {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b ^ 3 ≤ c) :
    Real.log a + 3 * Real.log b ≤ Real.log c := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h' : (a : ℝ) * (b : ℝ) ^ 3 ≤ c := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rwa [Real.log_mul ha'.ne' (by positivity), Real.log_pow] at this

lemma N_pos {v : ℕ} (hv : Admissible v) : 1 ≤ N v := by
  have hv0 : 0 < v := by unfold Admissible at hv; omega
  obtain ⟨B, hB⟩ := (sts_exists_iff v hv0).2 hv
  rw [N, Nat.one_le_iff_ne_zero, Nat.card_ne_zero]
  exact ⟨⟨Quotient.mk _ ⟨B, hB⟩⟩, inferInstance⟩

lemma log_D7_le {v : ℕ} (hv : 15 ≤ v) (ha : Admissible v) :
    Real.log (D7 v) ≤ v * Real.log v + Real.log (N v) := by
  have h1 : ((D7 v : ℕ) : ℝ) ≤ (v : ℝ) ^ v * (N v : ℝ) := by exact_mod_cast D7_le v
  have h2 : (0 : ℝ) < D7 v := by exact_mod_cast lemma4 v hv ha
  have h3 : (0 : ℝ) < N v := by exact_mod_cast N_pos ha
  have h4 : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have := Real.log_le_log h2 h1
  rwa [Real.log_mul (by positivity) h3.ne', Real.log_pow] at this

lemma rpow_le_of_log {b e : ℝ} {M : ℕ} (hb : 0 < b) (hM : 1 ≤ M)
    (h : e * Real.log b ≤ Real.log M) : b ^ e ≤ M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Real.rpow_def_of_pos hb, ← Real.exp_log hM']
  exact Real.exp_le_exp.2 (by linarith)

lemma log_D7_nonneg {v : ℕ} (hv : 15 ≤ v) (ha : Admissible v) : 0 ≤ Real.log (D7 v) :=
  Real.log_nonneg (by exact_mod_cast lemma4 v hv ha)

/-- Inequality (4.3) in the proof of Theorem 2. -/
theorem D7_lower (α : ℝ) (hα : 0 ≤ α)
    (hL : ∀ n : ℕ, 1 ≤ n → α * (n : ℝ) ^ 2 * (Real.log n - 2) ≤ Real.log (L n))
    (v : ℕ) (hv : 15 ≤ v) (ha : Admissible v) :
    α / 6 * (v : ℝ) ^ 2 * (Real.log v - 4.5) ≤ Real.log (D7 v) := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  by_cases hsmall : Real.log v ≤ 4.5
  · have : α / 6 * (v : ℝ) ^ 2 * (Real.log v - 4.5) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith [log_D7_nonneg hv ha]
  push_neg at hsmall
  have hv80 : 80 ≤ v := by
    by_contra hcon
    have : (v : ℝ) ≤ 79 := by exact_mod_cast (show v ≤ 79 by omega)
    have h0 : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
    have := Real.log_le_log h0 this
    have h79 : Real.log 79 < 4.5 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]; exact exp_four_half_gt
    linarith
  obtain ⟨n, w, hw, hv', hu, -, -⟩ := table v hv ha
  have hw7 : w ≤ 7 := by simp only [mem_insert, mem_singleton] at hw; omega
  have hcon := construction_D7 w n hw (by omega)
  rw [show w + n = n + w by ring, ← hv'] at hcon
  have hlog := log_mul_pow_le (L_pos n) (lemma4 (n + w) (by omega) hu) hcon
  have hLn := hL n (by omega)
  have hih := ih (n + w) (by omega) (by omega) hu
  have hkey := key_ineq (n : ℝ) (w : ℝ) (by exact_mod_cast (show 20 ≤ n by omega))
    (by positivity) (by exact_mod_cast hw7)
  have hvr : (v : ℝ) = 3 * n + w := by exact_mod_cast hv'
  push_cast at hih
  rw [hvr]
  nlinarith [mul_le_mul_of_nonneg_left hkey (show 0 ≤ α / 6 by positivity)]

/-- The implication (4.1) ⇒ (4.2) in the proof of Theorem 2: if `α ≥ 1/2` and
`log L(n) ≥ α n² (log n - 2)` for all `n ≥ 1`, then `log N(v) ≥ (α/6) v² (log v - 5)` for every
admissible `v`. -/
theorem lowerBound_of_latin (α : ℝ) (hα : 1 / 2 ≤ α)
    (hL : ∀ n : ℕ, 1 ≤ n → α * (n : ℝ) ^ 2 * (Real.log n - 2) ≤ Real.log (L n))
    (v : ℕ) (hv : Admissible v) :
    α / 6 * (v : ℝ) ^ 2 * (Real.log v - 5) ≤ Real.log (N v) := by
  have hN : 0 ≤ Real.log (N v) := Real.log_natCast_nonneg _
  by_cases hsmall : Real.log v ≤ 5
  · have : α / 6 * (v : ℝ) ^ 2 * (Real.log v - 5) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  push_neg at hsmall
  have hv143 : 143 ≤ v := by
    by_contra hcon
    have : (v : ℝ) ≤ 142 := by exact_mod_cast (show v ≤ 142 by omega)
    have h0 : (0 : ℝ) < v := by
      rcases Nat.eq_zero_or_pos v with h | h
      · subst h; simp at hsmall; linarith
      · exact_mod_cast h
    have := Real.log_le_log h0 this
    have h142 : Real.log 142 < 5 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]; linarith [exp_five_gt]
    linarith
  have h1 := D7_lower α (by linarith) hL v (by omega) hv
  have h2 := log_D7_le (by omega) hv
  have hvr : (122 : ℝ) ≤ v := by exact_mod_cast (show 122 ≤ v by omega)
  have h3 := log_le_div_24 v hvr
  have h4 : (v : ℝ) * Real.log v ≤ α / 6 * (v : ℝ) ^ 2 * (1 / 2) := by
    have : Real.log v ≤ α / 12 * v := by nlinarith
    nlinarith
  nlinarith

lemma hL_half (n : ℕ) (hn : 1 ≤ n) :
    1 / 2 * (n : ℝ) ^ 2 * (Real.log n - 2) ≤ Real.log (L n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < Real.exp (-2) * n := by positivity
  have := Real.log_le_log (Real.rpow_pos_of_pos hb _) (lemma2 n)
  rw [Real.log_rpow hb, Real.log_mul (by positivity) hn'.ne', Real.log_exp] at this
  linarith

lemma hL_one (h : vdWPC) (n : ℕ) (hn : 1 ≤ n) :
    1 * (n : ℝ) ^ 2 * (Real.log n - 2) ≤ Real.log (L n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < Real.exp (-2) * n := by positivity
  have := Real.log_le_log (pow_pos hb _) (lemma2_vdW h n)
  rw [Real.log_pow, Real.log_mul (by positivity) hn'.ne', Real.log_exp] at this
  push_cast at this
  linarith

lemma theorem2_gen (α : ℝ) (hα : 1 / 2 ≤ α)
    (hL : ∀ n : ℕ, 1 ≤ n → α * (n : ℝ) ^ 2 * (Real.log n - 2) ≤ Real.log (L n))
    (v : ℕ) (hv : Admissible v) :
    (Real.exp (-5) * v) ^ (α / 6 * (v : ℝ) ^ 2) ≤ N v := by
  have hv0 : (0 : ℝ) < v := by
    have : 0 < v := by unfold Admissible at hv; omega
    exact_mod_cast this
  refine rpow_le_of_log (by positivity) (N_pos hv) ?_
  rw [Real.log_mul (by positivity) hv0.ne', Real.log_exp]
  have := lowerBound_of_latin α hα hL v hv
  linarith

/-- **Theorem 2**, first part (inequality (1.3)): `N(v) ≥ (e^{-5} v)^{v²/12}`. -/
theorem theorem2 (v : ℕ) (hv : Admissible v) :
    (Real.exp (-5) * v) ^ ((v : ℝ) ^ 2 / 12) ≤ N v := by
  have := theorem2_gen (1 / 2) le_rfl hL_half v hv
  convert this using 2; ring

/-- **Theorem 2**, second part: if the vdWPC is valid, `N(v) ≥ (e^{-5} v)^{v²/6}`. -/
theorem theorem2_vdW (h : vdWPC) (v : ℕ) (hv : Admissible v) :
    (Real.exp (-5) * v) ^ ((v : ℝ) ^ 2 / 6) ≤ N v := by
  have := theorem2_gen 1 (by norm_num) (hL_one h) v hv
  convert this using 2; ring

/-- `PD α c`: for all sufficiently large admissible `v`, `log D₇(v) ≥ (α/6) v² (log v - c)`. -/
def PD (α c : ℝ) : Prop :=
  ∃ V : ℕ, ∀ v : ℕ, V ≤ v → Admissible v → α / 6 * (v : ℝ) ^ 2 * (Real.log v - c) ≤ Real.log (D7 v)

lemma PD_mono {α c c' : ℝ} (hα : 0 ≤ α) (hc : c ≤ c') : PD α c → PD α c' := by
  rintro ⟨V, hV⟩
  refine ⟨V, fun v hv ha => le_trans ?_ (hV v hv ha)⟩
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

lemma PD_step {α c δ : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ)
    (hL : ∀ n : ℕ, 1 ≤ n → α * (n : ℝ) ^ 2 * (Real.log n - 2) ≤ Real.log (L n)) :
    PD α c → PD α (Real.log 3 + 4 / 3 + c / 3 + δ) := by
  rintro ⟨V, hV⟩
  obtain ⟨V0, hV0⟩ := step_ineq c δ hδ
  refine ⟨max (max 45 (3 * V)) ⌈V0⌉₊, fun v hv ha => ?_⟩
  simp only [max_le_iff] at hv
  obtain ⟨⟨hv45, hvV⟩, hvV0⟩ := hv
  obtain ⟨u, n, hu, hcon, -, hu1, -, hn1⟩ := lemma3 v (by omega) ha
  have hvr45 : (45 : ℝ) ≤ v := by exact_mod_cast hv45
  have hvrV : 3 * (V : ℝ) ≤ v := by exact_mod_cast hvV
  have hu15 : 15 ≤ u := by
    have : (15 : ℝ) ≤ u := by linarith
    exact_mod_cast this
  have huV : V ≤ u := by
    have : (V : ℝ) ≤ u := by linarith
    exact_mod_cast this
  have hn : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hlog := log_mul_pow_le (L_pos n) (lemma4 u hu15 hu) hcon
  have hLn := hL n hn
  have hih := hV u huV hu
  have hstep := hV0 v n u ((Nat.le_ceil V0).trans (by exact_mod_cast hvV0)) hn1 hu1
  nlinarith [mul_le_mul_of_nonneg_left hstep (show 0 ≤ α / 6 by positivity)]

lemma PD_iter {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ)
    (hL : ∀ n : ℕ, 1 ≤ n → α * (n : ℝ) ^ 2 * (Real.log n - 2) ≤ Real.log (L n)) (k : ℕ) :
    PD α (3 / 2 * Real.log 3 + 2 + 3 / 2 * δ + 3 / 3 ^ k) := by
  induction k with
  | zero =>
    refine PD_mono hα ?_ ⟨15, fun v hv ha => D7_lower α hα hL v hv ha⟩
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
    norm_num; linarith
  | succ k ih =>
    refine PD_mono hα (le_of_eq ?_) (PD_step hα hδ hL ih)
    rw [pow_succ]; field_simp; ring

lemma K_eq : (3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2) = Real.exp (-(3 / 2 * Real.log 3 + 2)) := by
  rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]; congr 1; ring

lemma theorem3_gen (α : ℝ) (hα : 0 < α)
    (hL : ∀ n : ℕ, 1 ≤ n → α * (n : ℝ) ^ 2 * (Real.log n - 2) ≤ Real.log (L n))
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < (3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2)) :
    ∀ᶠ v : ℕ in atTop, Admissible v →
      (((3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2) - ε) * v) ^ (α / 6 * (v : ℝ) ^ 2) ≤ N v := by
  set K := (3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2) with hKdef
  set cs := 3 / 2 * Real.log 3 + 2 with hcs
  have hK : Real.log K = -cs := by rw [hKdef, K_eq, Real.log_exp]
  have hKε : 0 < K - ε := by linarith
  set δ := (Real.log K - Real.log (K - ε)) / 3 with hδdef
  have hδ : 0 < δ := by
    have := Real.log_lt_log hKε (show K - ε < K by linarith)
    rw [hδdef]; linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (6 / δ) (show (1 : ℝ) < 3 by norm_num)
  have hk' : 3 / (3 : ℝ) ^ k ≤ δ / 2 := by
    have h3 : (0 : ℝ) < 3 ^ k := by positivity
    rw [div_le_iff₀ h3]
    have : 6 / δ * δ = 6 := by field_simp
    nlinarith
  obtain ⟨V, hV⟩ := PD_mono (c' := cs + 2 * δ) hα.le (by linarith) (PD_iter hα.le hδ hL k)
  have hB := tendsto_natCast_atTop_atTop.eventually
    (Real.isLittleO_log_id_atTop.bound (c := α / 6 * δ) (by positivity))
  filter_upwards [hB, eventually_ge_atTop (max V 15)] with v hB hv ha
  rw [max_le_iff] at hv
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hlv0 : 0 ≤ Real.log v := Real.log_natCast_nonneg v
  simp only [Real.norm_eq_abs, id, abs_of_nonneg hlv0, abs_of_pos hv0] at hB
  refine rpow_le_of_log (by positivity) (N_pos ha) ?_
  rw [Real.log_mul hKε.ne' hv0.ne']
  have hlKε : Real.log (K - ε) = -cs - 3 * δ := by rw [hδdef, hK]; ring
  rw [hlKε]
  have h1 := hV v hv.1 ha
  have h2 := log_D7_le hv.2 ha
  have h3 : (v : ℝ) * Real.log v ≤ α / 6 * δ * (v : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- **Theorem 3**, first part: for any `ε > 0` (small enough that the base is positive) and all
sufficiently large admissible `v`, `N(v) ≥ ((3^{-3/2} e^{-2} - ε) v)^{v²/12}`. -/
theorem theorem3 (ε : ℝ) (hε : 0 < ε) (hε' : ε < (3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2)) :
    ∀ᶠ v : ℕ in atTop, Admissible v →
      (((3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2) - ε) * v) ^ ((v : ℝ) ^ 2 / 12) ≤ N v := by
  filter_upwards [theorem3_gen (1 / 2) (by norm_num) hL_half ε hε hε'] with v hv ha
  convert hv ha using 2; ring

/-- **Theorem 3**, second part (inequality (1.2)): if the vdWPC is valid, then for any `ε > 0`
(small enough that the base is positive) and all sufficiently large admissible `v`,
`N(v) ≥ ((3^{-3/2} e^{-2} - ε) v)^{v²/6}`. -/
theorem theorem3_vdW (h : vdWPC) (ε : ℝ) (hε : 0 < ε)
    (hε' : ε < (3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2)) :
    ∀ᶠ v : ℕ in atTop, Admissible v →
      (((3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2) - ε) * v) ^ ((v : ℝ) ^ 2 / 6) ≤ N v := by
  filter_upwards [theorem3_gen 1 (by norm_num) (hL_one h) ε hε hε'] with v hv ha
  convert hv ha using 2; ring

end STS
