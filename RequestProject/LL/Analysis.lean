/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Real-analytic estimates for the Linial–Luria bounds

* `log_jensen` : Jensen's inequality for `log (1 + ·)` on a finite set.
* `weighted_log_sum_le` : the comparison of the Riemann-type sums
  `∑_{r=1}^{L} (r^{d-1}/L^d) log (1 + c (r/L)^d)` with the corresponding integral
  `∫₀^s u^{d-1} log(1 + c u^d) du`, `s = (L+1)/L`, followed by an elementary bound.
-/

@[expose] public section

open Finset Real

namespace LinialLuria

/-- Jensen's inequality for the concave function `log (1 + ·)`. -/
lemma log_jensen {γ : Type*} (B : Finset γ) (g : γ → ℝ) (hg : ∀ x ∈ B, 0 ≤ g x) :
    ∑ x ∈ B, Real.log (1 + g x) ≤ B.card * Real.log (1 + (∑ x ∈ B, g x) / B.card) := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp
  have hd : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := B)
    (w := fun _ => (1 : ℝ) / B.card) (p := fun x => 1 + g x) (by intros; positivity)
    (by rw [sum_const, nsmul_eq_mul]; field_simp)
    (by intro x hx; simp only [Set.mem_Ioi]; linarith [hg x hx])
  simp only [smul_eq_mul] at hJ
  rw [← mul_sum, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one] at hJ
  have h1 : 1 / (B.card : ℝ) * (B.card + ∑ x ∈ B, g x) = 1 + (∑ x ∈ B, g x) / B.card := by
    field_simp
  rw [h1] at hJ
  have := (mul_le_mul_iff_of_pos_left hd).2 hJ
  rw [← mul_assoc, mul_one_div_cancel hd.ne', one_mul] at this
  exact this

/-- The function `G(x) = (1 + x) log (1 + x) - x`, an antiderivative of `log (1 + x)`. -/
noncomputable def Gfun (x : ℝ) : ℝ := (1 + x) * Real.log (1 + x) - x

lemma Gfun_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Gfun x := by
  unfold Gfun
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + x by linarith)
  have h1 : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  rw [h1] at h
  have h2 : x ≤ (1 + x) * Real.log (1 + x) := by
    rw [div_le_iff₀ (by linarith)] at h; linarith
  linarith

lemma log_one_add_le_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ Real.sqrt x := by
  set y := Real.sqrt x with hy
  have hy0 : 0 ≤ y := Real.sqrt_nonneg x
  have hxy : x = y ^ 2 := (Real.sq_sqrt hx).symm
  have hexp : 1 + y ^ 2 ≤ Real.exp y := by
    have := Real.sum_le_exp_of_nonneg hy0 4
    simp [Finset.sum_range_succ, Nat.factorial] at this
    nlinarith [sq_nonneg (y - 3/2), mul_nonneg hy0 (sq_nonneg (y-3/2))]
  rw [hxy]
  calc Real.log (1 + y ^ 2) ≤ Real.log (Real.exp y) := Real.log_le_log (by positivity) hexp
    _ = y := Real.log_exp y

lemma Gfun_le {x : ℝ} (hx : 0 ≤ x) : Gfun x ≤ x * Real.log (1 + x) - x + Real.sqrt x := by
  unfold Gfun
  have := log_one_add_le_sqrt hx
  nlinarith

/-- The derivative of the antiderivative used in `weighted_log_sum_le`. -/
lemma hasDerivAt_antider (d : ℕ) (hd : 1 ≤ d) (κ c : ℝ) (hκ : 0 < κ) (hc : 0 < c) (u : ℝ)
    (hu : 0 ≤ u) :
    HasDerivAt (fun u : ℝ => Gfun (κ * u ^ d) / (d * c))
      ((κ / c) * u ^ (d - 1) * Real.log (1 + κ * u ^ d)) u := by
  have hpos : 0 < 1 + κ * u ^ d := by positivity
  have h1 : HasDerivAt (fun u : ℝ => 1 + κ * u ^ d) (κ * (d * u ^ (d - 1))) u := by
    simpa using ((hasDerivAt_pow d u).const_mul κ).const_add 1
  have h2 := ((h1.mul (h1.log hpos.ne')).sub (((hasDerivAt_pow d u).const_mul κ))).div_const
    (d * c)
  unfold Gfun
  convert h2 using 1
  have hd' : (d : ℝ) ≠ 0 := by
    have : (0:ℝ) < d := by exact_mod_cast hd
    exact this.ne'
  field_simp
  ring

lemma sqrt_div_eq (c y : ℝ) (hc : 0 < c) (hy : 0 ≤ y) :
    Real.sqrt (c * y) / c = Real.sqrt (y / c) := by
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity)]
  field_simp

/-- **Sum–integral comparison.** For `d ≥ 1`, `L ≥ 1`, `c > 0` and `s = (L+1)/L`,
`∑_{r=1}^{L} (r^{d-1}/L^d) log (1 + c (r/L)^d) ≤ (s^d/d)(log(1 + c s^d) - 1) + √(s^d/c)/d`. -/
lemma weighted_log_sum_le (d L : ℕ) (hd : 1 ≤ d) (hL : 1 ≤ L) (c : ℝ) (hc : 0 < c) :
    ∑ r ∈ range L, ((r + 1 : ℝ) ^ (d - 1) / (L : ℝ) ^ d) *
        Real.log (1 + c * ((r + 1 : ℝ) / L) ^ d) ≤
      (((L + 1 : ℝ) / L) ^ d / d) * (Real.log (1 + c * ((L + 1 : ℝ) / L) ^ d) - 1) +
        Real.sqrt (((L + 1 : ℝ) / L) ^ d / c) / d := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set κ : ℝ := c / (L : ℝ) ^ d with hκ
  have hκpos : 0 < κ := by positivity
  set A : ℝ → ℝ := fun u => Gfun (κ * u ^ d) / (d * c) with hA
  set f : ℝ → ℝ := fun u => (κ / c) * u ^ (d - 1) * Real.log (1 + κ * u ^ d) with hf
  have hderiv : ∀ u : ℝ, 0 ≤ u → HasDerivAt A (f u) u := fun u hu =>
    hasDerivAt_antider d hd κ c hκpos hc u hu
  have hterm : ∀ r : ℕ, ((r + 1 : ℝ) ^ (d - 1) / (L : ℝ) ^ d) *
      Real.log (1 + c * ((r + 1 : ℝ) / L) ^ d) = f (r + 1) := by
    intro r
    simp only [hf, hκ]
    rw [div_pow]
    field_simp
  have hmono : ∀ u v : ℝ, 0 ≤ u → u ≤ v → f u ≤ f v := by
    intro u v hu huv
    simp only [hf]
    have h1 : u ^ (d - 1) ≤ v ^ (d - 1) := pow_le_pow_left₀ hu huv _
    have h2 : Real.log (1 + κ * u ^ d) ≤ Real.log (1 + κ * v ^ d) := by
      apply Real.log_le_log (by have := mul_nonneg hκpos.le (pow_nonneg hu d); linarith)
      have := pow_le_pow_left₀ hu huv d
      nlinarith
    have h3 : 0 ≤ Real.log (1 + κ * u ^ d) := Real.log_nonneg (by
      have : 0 ≤ κ * u ^ d := mul_nonneg hκpos.le (pow_nonneg hu d)
      linarith)
    have h4 : 0 ≤ κ / c := by positivity
    have := mul_le_mul h1 h2 h3 (pow_nonneg (hu.trans huv) _)
    calc κ / c * u ^ (d - 1) * Real.log (1 + κ * u ^ d)
        = κ / c * (u ^ (d - 1) * Real.log (1 + κ * u ^ d)) := by ring
      _ ≤ κ / c * (v ^ (d - 1) * Real.log (1 + κ * v ^ d)) :=
          mul_le_mul_of_nonneg_left this h4
      _ = _ := by ring
  have hstep : ∀ r : ℕ, f (r + 1) ≤ A (r + 2) - A (r + 1) := by
    intro r
    have hlt : (r + 1 : ℝ) < r + 2 := by linarith
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope A f hlt
      (fun x hx => (hderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => hderiv x (by linarith [hx.1]))
    have : (r + 2 : ℝ) - (r + 1) = 1 := by ring
    rw [this, div_one] at hξeq
    rw [← hξeq]
    exact hmono _ _ (by positivity) hξ.1.le
  have hsum : ∑ r ∈ range L, f (r + 1) ≤ A (L + 1) - A 1 := by
    have := sum_le_sum (fun r (_ : r ∈ range L) => hstep r)
    refine this.trans (le_of_eq ?_)
    have h := sum_range_sub (fun r : ℕ => A ((r : ℝ) + 1)) L
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at h
    rw [← h]
    apply sum_congr rfl
    intro r _
    ring_nf
  have hA1 : 0 ≤ A 1 := by
    simp only [hA]
    exact div_nonneg (Gfun_nonneg (by positivity)) (by positivity)
  have hAL : A (L + 1) = Gfun (c * ((L + 1 : ℝ) / L) ^ d) / (d * c) := by
    simp only [hA, hκ]
    congr 2
    rw [div_pow]; field_simp
  set y := ((L + 1 : ℝ) / L) ^ d with hy
  have hy0 : 0 ≤ y := by positivity
  have hG := Gfun_le (show 0 ≤ c * y by positivity)
  rw [sum_congr rfl (fun r _ => hterm r)]
  have hsq := sqrt_div_eq c y hc hy0
  calc ∑ r ∈ range L, f (r + 1) ≤ A (L + 1) := by linarith
    _ = Gfun (c * y) / (d * c) := hAL
    _ ≤ (c * y * Real.log (1 + c * y) - c * y + Real.sqrt (c * y)) / (d * c) :=
        div_le_div_of_nonneg_right hG (by positivity)
    _ = y / d * (Real.log (1 + c * y) - 1) + (Real.sqrt (c * y) / c) / d := by
        field_simp
    _ = _ := by rw [hsq]

end LinialLuria
