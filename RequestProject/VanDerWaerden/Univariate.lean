/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Univariate lemmas for Gurvits's proof of the van der Waerden permanent theorem

* `VdW.norm_eval_le_of_roots_im_nonpos` : if all roots of a complex polynomial lie in the
  closed lower half-plane, then `|P|` does not decrease when moving upwards from the closed upper
  half-plane.
* `VdW.univariate_key` : the key univariate inequality (Gurvits; Laurent–Schrijver): if
  `g(t) = c ∏ (t + rᵢ)` with `c, rᵢ ≥ 0`, at most `m` factors, and `g(t) ≥ M t` for `t > 0`, then
  `g'(0) ≥ ((m - 1)/m)^(m - 1) M`.
-/

@[expose] public section

open Polynomial Complex

namespace VdW

/-- If all roots of `P` have nonpositive imaginary part, then `‖P(w)‖ ≤ ‖P(w + i y)‖` for
`Im w ≥ 0` and `y ≥ 0`. -/
theorem norm_eval_le_of_roots_im_nonpos (P : ℂ[X]) (hP : ∀ ρ ∈ P.roots, ρ.im ≤ 0) (w : ℂ)
    (hw : 0 ≤ w.im) (y : ℝ) (hy : 0 ≤ y) : ‖P.eval w‖ ≤ ‖P.eval (w + y * I)‖ := by
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := P))
  rw [← hfac]
  simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub,
    eval_X, norm_mul]
  gcongr
  rw [Multiset.norm_prod, Multiset.norm_prod]
  simp only [Multiset.map_map, Function.comp_def]
  apply Multiset.prod_map_le_prod_map₀
  · intros; positivity
  · intro ρ hρ
    have h1 := hP ρ hρ
    have key : ‖w - ρ‖ ^ 2 ≤ ‖w + y * I - ρ‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 key

/-- One step of the AM-GM inequality in the form needed below. -/
lemma amgm_step (a S : ℝ) (j : ℕ) (ha : 0 ≤ a) (hS : 0 ≤ S) :
    (1 + a) * (1 + S / j) ^ j ≤ (1 + (a + S) / (j + 1 : ℕ)) ^ (j + 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp; linarith
  set B := 1 + S / j with hB
  set C := 1 + (a + S) / (j + 1 : ℕ) with hC
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hBpos : 0 < B := by positivity
  have hCpos : 0 < C := by positivity
  have h1a : 1 + a = (j + 1) * C - j * B := by
    rw [hB, hC]; push_cast; field_simp; ring
  have bern := one_add_mul_le_pow (show (-2 : ℝ) ≤ C / B - 1 by
    have : 0 < C / B := by positivity
    linarith) j
  have hx : (1 + (C / B - 1)) = C / B := by ring
  rw [hx, div_pow] at bern
  rw [le_div_iff₀ (by positivity)] at bern
  rw [h1a, pow_succ]
  have key : ((j + 1) * C - j * B) * B ^ j ≤ C * ((1 + j * (C / B - 1)) * B ^ j) := by
    have : C * ((1 + j * (C / B - 1)) * B ^ j) - ((j + 1) * C - j * B) * B ^ j
        = j * (C - B) ^ 2 / B * B ^ j := by field_simp; ring
    have : 0 ≤ j * (C - B) ^ 2 / B * B ^ j := by positivity
    linarith
  calc _ ≤ _ := key
    _ ≤ C * C ^ j := by gcongr
    _ = C ^ j * C := by ring

/-- AM-GM: `∏ (1 + xᵢ) ≤ (1 + (∑ xᵢ)/k)^k` for `k` nonnegative numbers `xᵢ`. -/
lemma amgm_multiset (t : Multiset ℝ) (ht : ∀ x ∈ t, 0 ≤ x) :
    (t.map (fun x => 1 + x)).prod ≤ (1 + t.sum / (Multiset.card t : ℕ)) ^ (Multiset.card t) := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha : 0 ≤ a := ht a (Multiset.mem_cons_self a t)
    have ht' : ∀ x ∈ t, 0 ≤ x := fun x hx => ht x (Multiset.mem_cons_of_mem hx)
    have hS : 0 ≤ t.sum := Multiset.sum_nonneg ht'
    calc (1 + a) * (t.map (fun x => 1 + x)).prod
        ≤ (1 + a) * (1 + t.sum / (Multiset.card t : ℕ)) ^ (Multiset.card t) :=
          mul_le_mul_of_nonneg_left (ih ht') (by linarith)
      _ ≤ _ := amgm_step a t.sum _ ha hS

/-- `(1 + S/j)^j` is nondecreasing in `j`. -/
lemma amgm_pad (S : ℝ) (hS : 0 ≤ S) (j m : ℕ) (hjm : j ≤ m) :
    (1 + S / j) ^ j ≤ (1 + S / m) ^ m := by
  induction m, hjm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    calc _ ≤ _ := ih
      _ = (1 + 0) * (1 + S / m) ^ m := by ring
      _ ≤ _ := by simpa using amgm_step 0 S m le_rfl hS

/-- The polynomial `∏_{r ∈ s} (X + r)`. -/
noncomputable def linProd (s : Multiset ℝ) : ℝ[X] := (s.map (fun r => X + C r)).prod

lemma linProd_eval (s : Multiset ℝ) (u : ℝ) :
    (linProd s).eval u = (s.map (fun r => u + r)).prod := by
  simp [linProd, eval_multiset_prod, Multiset.map_map]

lemma linProd_cons (a : ℝ) (s : Multiset ℝ) : linProd (a ::ₘ s) = (X + C a) * linProd s := by
  simp [linProd]

lemma linProd_eval_pos (s : Multiset ℝ) (hs : ∀ r ∈ s, 0 < r) (u : ℝ) :
    (linProd s).eval u = s.prod * (s.map (fun r => 1 + u / r)).prod := by
  rw [linProd_eval]
  have : s.prod = (s.map id).prod := by simp
  rw [this, ← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro r hr
  have := hs r hr
  simp only [id]
  field_simp
  ring

lemma linProd_deriv_pos (s : Multiset ℝ) (hs : ∀ r ∈ s, 0 < r) :
    (derivative (linProd s)).eval 0 = s.prod * (s.map (fun r => 1 / r)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [linProd]
  | cons a s ih =>
    have ha : 0 < a := hs a (Multiset.mem_cons_self a s)
    have ih' := ih (fun r hr => hs r (Multiset.mem_cons_of_mem hr))
    rw [linProd_cons, derivative_mul]
    simp only [derivative_add, derivative_X, derivative_C, add_zero, one_mul, eval_add, eval_mul,
      eval_X, eval_C, zero_add, ih', Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    rw [linProd_eval]
    simp only [zero_add, Multiset.map_id']
    field_simp

lemma le_of_forall_mul_le_add {M A B : ℝ} (h : ∀ u : ℝ, 0 < u → M * u ≤ A + B * u) : M ≤ B := by
  by_contra hMB
  have hpos : 0 < M - B := by linarith [not_le.1 hMB]
  have := h ((|A| + 1) / (M - B)) (by positivity)
  have e : M * ((|A| + 1) / (M - B)) = B * ((|A| + 1) / (M - B)) + (|A| + 1) := by
    field_simp; ring
  rw [e] at this
  linarith [le_abs_self A]

lemma univariate_zero_root (c : ℝ) (s : Multiset ℝ) (h0 : (0 : ℝ) ∈ s) (m : ℕ) (M : ℝ)
    (hM : 0 ≤ M) (hg : ∀ u : ℝ, 0 < u → M * u ≤ (C c * linProd s).eval u) :
    ((m - 1 : ℝ) / m) ^ (m - 1) * M ≤ (derivative (C c * linProd s)).eval 0 := by
  obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem h0
  set h := C c * linProd s' with hh
  have e : C c * linProd (0 ::ₘ s') = X * h := by
    rw [linProd_cons, hh]; simp; ring
  rw [e] at hg ⊢
  simp only [derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X, zero_mul,
    add_zero]
  have hMh : ∀ u : ℝ, 0 < u → M ≤ h.eval u := by
    intro u hu
    have := hg u hu
    simp only [eval_mul, eval_X] at this
    nlinarith
  have hlim : Filter.Tendsto (fun u => h.eval u) (nhdsWithin 0 (Set.Ioi 0)) (nhds (h.eval 0)) :=
    (h.continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  have hM0 : M ≤ h.eval 0 :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun u hu => hMh u hu)
  have hq : ((m - 1 : ℝ) / m) ^ (m - 1) ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    apply pow_le_one₀
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      apply div_nonneg <;> linarith
    · rw [div_le_one (by exact_mod_cast hm)]; linarith
  nlinarith

lemma univariate_pos_roots (c : ℝ) (s : Multiset ℝ) (hc : 0 ≤ c) (hs : ∀ r ∈ s, 0 < r)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Multiset.card s ≤ m) (M : ℝ) (hM : 0 ≤ M)
    (hg : ∀ u : ℝ, 0 < u → M * u ≤ (C c * linProd s).eval u) :
    ((m - 1 : ℝ) / m) ^ (m - 1) * M ≤ (derivative (C c * linProd s)).eval 0 := by
  set P0 := s.prod with hP0
  set S1 := (s.map (fun r => 1 / r)).sum with hS1
  have hP0pos : 0 < P0 := Multiset.prod_pos hs
  have hS1nn : 0 ≤ S1 := Multiset.sum_nonneg (fun x hx => by
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx; exact (one_div_pos.2 (hs r hr)).le)
  rw [derivative_C_mul, eval_mul, eval_C, linProd_deriv_pos s hs]
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hub : ∀ u : ℝ, 0 < u → M * u ≤ c * P0 * (1 + u * S1 / m) ^ m := by
    intro u hu
    have h1 := hg u hu
    rw [eval_mul, eval_C, linProd_eval_pos s hs] at h1
    have hprod : (s.map (fun r => 1 + u / r)).prod ≤ (1 + u * S1 / m) ^ m := by
      have e1 : s.map (fun r => 1 + u / r) = (s.map (fun r => u / r)).map (fun x => 1 + x) := by
        simp [Multiset.map_map]
      have e2 : (s.map (fun r => u / r)).sum = u * S1 := by
        rw [hS1, ← Multiset.sum_map_mul_left]
        congr 1
        apply Multiset.map_congr rfl
        intros; ring
      rw [e1]
      calc _ ≤ _ := amgm_multiset _ (fun x hx => by
              obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx; exact (div_pos hu (hs r hr)).le)
        _ ≤ _ := by
          rw [e2, Multiset.card_map]
          exact amgm_pad _ (by positivity) _ _ hcard
    calc M * u ≤ _ := h1
      _ = c * P0 * (s.map (fun r => 1 + u / r)).prod := by ring
      _ ≤ _ := by gcongr
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · have hm1' : m = 1 := by omega
    subst hm1'
    simp only [Nat.cast_one, sub_self, zero_div, Nat.sub_self, pow_zero, one_mul]
    apply le_of_forall_mul_le_add (A := c * P0)
    intro u hu
    have := hub u hu
    simp only [Nat.cast_one, div_one, pow_one] at this
    linarith
  rcases hS1nn.lt_or_eq with hS1pos | hS1zero
  · have hm2r : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    set q : ℝ := (m - 1) / m with hq
    have hqpos : 0 < q := by rw [hq]; apply div_pos <;> linarith
    have hu := hub (1 / (q * S1)) (by positivity)
    have hm1ne : (m : ℝ) - 1 ≠ 0 := by linarith
    have e1 : 1 + 1 / (q * S1) * S1 / m = 1 / q := by
      rw [hq]; field_simp; ring
    rw [e1] at hu
    have hm1 : (m - 1 : ℕ) + 1 = m := by omega
    have e2' : ∀ k : ℕ, q ^ k * (1 / q) ^ (k + 1) = 1 / q := by
      intro k; rw [pow_succ, one_div_pow]; field_simp
    have e2 : q ^ (m - 1) * (1 / q) ^ m = 1 / q := by
      have := e2' (m - 1); rwa [hm1] at this
    have h3 : q ^ (m - 1) * (M * (1 / (q * S1))) ≤ q ^ (m - 1) * (c * P0 * (1 / q) ^ m) := by
      gcongr
    have h4 : q ^ (m - 1) * (c * P0 * (1 / q) ^ m) = c * P0 / q := by
      rw [show q ^ (m - 1) * (c * P0 * (1 / q) ^ m) = c * P0 * (q ^ (m - 1) * (1 / q) ^ m) by
        ring, e2]; ring
    rw [h4] at h3
    have h5 : q ^ (m - 1) * (M * (1 / (q * S1))) = q ^ (m - 1) * M / (q * S1) := by ring
    rw [h5, div_le_div_iff₀ (by positivity) hqpos] at h3
    have : q ^ (m - 1) * M * q ≤ c * (P0 * S1) * q := by nlinarith
    exact le_of_mul_le_mul_right this hqpos
  · have hM0 : M ≤ 0 := by
      apply le_of_forall_mul_le_add (A := c * P0)
      intro u hu
      have := hub u hu
      rw [← hS1zero] at this
      simpa using this
    have : M = 0 := le_antisymm hM0 hM
    rw [this, mul_zero]
    exact mul_nonneg hc (mul_nonneg hP0pos.le hS1nn)

/-- **Key univariate inequality** (Gurvits; Laurent–Schrijver). Let `g = c ∏_{r ∈ s} (X + r)`
with `c ≥ 0`, all `r ≥ 0` and at most `m ≥ 1` factors. If `M t ≤ g(t)` for all `t > 0`
(with `M ≥ 0`), then `((m - 1)/m)^(m - 1) M ≤ g'(0)`. -/
theorem univariate_key (c : ℝ) (s : Multiset ℝ) (hc : 0 ≤ c) (hs : ∀ r ∈ s, 0 ≤ r)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Multiset.card s ≤ m) (M : ℝ) (hM : 0 ≤ M)
    (hg : ∀ u : ℝ, 0 < u → M * u ≤ (C c * linProd s).eval u) :
    ((m - 1 : ℝ) / m) ^ (m - 1) * M ≤ (derivative (C c * linProd s)).eval 0 := by
  by_cases h0 : (0 : ℝ) ∈ s
  · exact univariate_zero_root c s h0 m M hM hg
  · exact univariate_pos_roots c s hc
      (fun r hr => lt_of_le_of_ne (hs r hr) (fun h => h0 (h ▸ hr))) m hm hcard M hM hg

end VdW
