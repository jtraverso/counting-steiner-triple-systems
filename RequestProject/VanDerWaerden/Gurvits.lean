/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.VanDerWaerden.Combinatorics

/-!
# Gurvits's proof of the van der Waerden bound for positive doubly stochastic matrices

Following L. Gurvits, as simplified by M. Laurent and A. Schrijver ("On Leonid Gurvits's proof
for permanents", Amer. Math. Monthly 117 (2010)), we show by descending induction on `k` that the
polynomials `q_k = VdW.qpoly A k` satisfy `CMono` and the capacity bound
`q_k(x) ≥ c_k ∏_{j<k} x_j` on the positive orthant, where `c_k = ∏_{k ≤ m < n} (m/(m+1))^m`.
For `k = 0` this gives `per A ≥ c_0 = n!/n^n`.

* `VdW.permanent_ge_of_pos` : `n!/n^n ≤ per A` for doubly stochastic `A` with positive entries.
-/

@[expose] public section

open Finset Polynomial Complex

namespace VdW

variable {n : ℕ}

/-- A real polynomial all of whose complex roots are real is a constant times a product of
linear factors `X + r`. -/
lemma real_factor (g : ℝ[X]) (hreal : ∀ ρ ∈ (g.map (algebraMap ℝ ℂ)).roots, ρ.im = 0) :
    g = C g.leadingCoeff * linProd ((g.map (algebraMap ℝ ℂ)).roots.map (fun ρ => -ρ.re)) := by
  set G := g.map (algebraMap ℝ ℂ) with hG
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := G))
  apply Polynomial.map_injective (algebraMap ℝ ℂ) (RingHom.injective _)
  rw [Polynomial.map_mul, map_C, linProd, Polynomial.map_multiset_prod, Multiset.map_map,
    Multiset.map_map]
  conv_lhs => rw [← hG, ← hfac]
  rw [hG, leadingCoeff_map]
  congr 2
  apply Multiset.map_congr rfl
  intro ρ hρ
  have hρ' : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hreal ρ hρ])
  simp only [Function.comp_apply, Polynomial.map_add, map_X, map_C]
  conv_lhs => rw [hρ']
  simp [sub_eq_add_neg]

lemma card_real_factor_le (g : ℝ[X]) :
    Multiset.card ((g.map (algebraMap ℝ ℂ)).roots.map (fun ρ => -ρ.re)) ≤ g.natDegree := by
  rw [Multiset.card_map]
  exact (card_roots' _).trans (natDegree_map_le)

/-- The constant `c_k = ∏_{k ≤ m < n} (m/(m+1))^m`. -/
noncomputable def vdwConst (n k : ℕ) : ℝ := ∏ m ∈ Finset.Ico k n, ((m : ℝ) / (m + 1)) ^ m

lemma vdwConst_self (n : ℕ) : vdwConst n n = 1 := by simp [vdwConst]

lemma vdwConst_succ {n k : ℕ} (hk : k < n) :
    vdwConst n k = ((k : ℝ) / (k + 1)) ^ k * vdwConst n (k + 1) := by
  rw [vdwConst, prod_eq_prod_Ico_succ_bot hk]
  rfl

lemma vdwConst_nonneg (n k : ℕ) : 0 ≤ vdwConst n k :=
  prod_nonneg (fun m _ => by positivity)

lemma vdwConst_pos {n k : ℕ} (hk : 1 ≤ k) : 0 < vdwConst n k :=
  prod_pos (fun m hm => by
    have : (1 : ℝ) ≤ m := by exact_mod_cast le_trans hk (mem_Ico.1 hm).1
    positivity)

lemma vdwConst_zero (n : ℕ) : vdwConst n 0 = (n.factorial : ℝ) / (n : ℝ) ^ n := by
  induction n with
  | zero => simp [vdwConst]
  | succ n ih =>
    rw [vdwConst, prod_Ico_succ_top (Nat.zero_le n), ← vdwConst, ih]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast [Nat.factorial_succ]
    rw [div_pow]
    field_simp
    ring

lemma norm_le_norm_add_mul_I (w : ℂ) (hw : 0 ≤ w.im) (t : ℝ) (ht : 0 ≤ t) :
    ‖w‖ ≤ ‖w + t * I‖ := by
  have key : ‖w‖ ^ 2 ≤ ‖w + t * I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 key

/-- `q_n = ∏ᵢ (A x)ᵢ` satisfies `CMono` when `A` has nonnegative entries. -/
theorem mono_qpoly_top (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    CMono (qpoly A n) := by
  intro z v hz hv
  rw [aeval_qpoly_top, aeval_qpoly_top, norm_prod, norm_prod]
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
  intro i _
  have e : ∑ j, algebraMap ℝ ℂ (A i j) * (z j + (v j : ℂ) * I) =
      ∑ j, algebraMap ℝ ℂ (A i j) * z j + ((∑ j, A i j * v j : ℝ) : ℂ) * I := by
    push_cast
    rw [sum_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    simp only [Complex.coe_algebraMap]
    ring
  rw [e]
  apply norm_le_norm_add_mul_I
  · rw [Complex.im_sum]
    apply sum_nonneg
    intro j _
    simp only [Complex.coe_algebraMap, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    exact mul_nonneg (hA i j) (hz j)
  · exact sum_nonneg (fun j _ => mul_nonneg (hA i j) (hv j))

/-- The capacity bound for `q_n = ∏ᵢ (A x)ᵢ`: weighted AM-GM. -/
theorem cap_qpoly_top (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin n))
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    ∏ j, x j ≤ MvPolynomial.eval x (qpoly A n) := by
  rw [mem_doublyStochastic_iff_sum] at hA
  obtain ⟨hnn, hrow, hcol⟩ := hA
  have h := aeval_qpoly_top A x
  change MvPolynomial.eval x (qpoly A n) = _ at h
  rw [h]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have hrow' : ∀ i, ∏ j, x j ^ A i j ≤ ∑ j, A i j * x j := fun i =>
    Real.geom_mean_le_arith_mean_weighted univ (A i) x (fun j _ => hnn i j) (hrow i)
      (fun j _ => (hx j).le)
  calc ∏ j, x j = ∏ j, x j ^ (∑ i, A i j) := by
        apply prod_congr rfl; intro j _; rw [hcol j, Real.rpow_one]
    _ = ∏ i, ∏ j, x j ^ A i j := by
        rw [prod_comm]
        apply prod_congr rfl; intro j _
        exact Real.rpow_sum_of_pos (hx j) _ _
    _ ≤ ∏ i, ∑ j, A i j * x j :=
        Finset.prod_le_prod₀
          (fun i _ => prod_nonneg (fun j _ => (Real.rpow_pos_of_pos (hx j) _).le))
          (fun i _ => hrow' i)

lemma filter_lt_succ (kk : Fin n) :
    univ.filter (fun j : Fin n => (j : ℕ) < (kk : ℕ) + 1) =
      insert kk (univ.filter (fun j : Fin n => (j : ℕ) < kk)) := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext h)
  · rintro (rfl | h) <;> omega

lemma prod_update_filter (x : Fin n → ℝ) (kk : Fin n) (u : ℝ) :
    ∏ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < (kk : ℕ) + 1), Function.update x kk u j =
      (∏ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < kk), x j) * u := by
  rw [filter_lt_succ, prod_insert (by simp), Function.update_self, mul_comm]
  congr 1
  apply prod_congr rfl
  intro j hj
  have : j ≠ kk := by
    intro h; simp only [mem_filter, mem_univ, true_and] at hj; rw [h] at hj; exact lt_irrefl _ hj
  rw [Function.update_of_ne this]

/-- The inductive statement of Gurvits's proof at level `k`. -/
def GurvitsInv (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Prop :=
  CMono (qpoly A k) ∧ ∀ x : Fin n → ℝ, (∀ j, 0 < x j) →
    vdwConst n k * ∏ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k), x j ≤
      MvPolynomial.eval x (qpoly A k)

theorem gurvitsInv_top (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    GurvitsInv A n := by
  refine ⟨mono_qpoly_top A (fun i j => nonneg_of_mem_doublyStochastic hA), fun x hx => ?_⟩
  rw [vdwConst_self, one_mul]
  have : univ.filter (fun j : Fin n => (j : ℕ) < n) = univ := by
    ext j; simp
  rw [this]
  exact cap_qpoly_top A hA x hx

theorem gurvitsInv_step (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j) (kk : Fin n)
    (h : GurvitsInv A ((kk : ℕ) + 1)) : GurvitsInv A kk := by
  obtain ⟨hmono, hcap⟩ := h
  have hpos : PosOn (qpoly A ((kk : ℕ) + 1)) := fun x hx =>
    lt_of_lt_of_le (mul_pos (vdwConst_pos (Nat.le_add_left 1 _))
      (prod_pos (fun j _ => hx j))) (hcap x hx)
  have hstab := stable_of_mono_pos hmono hpos
  have hstabD := stable_pderiv hstab kk (fun z => degree_line_qpoly_pos A hA z kk)
  have hmonoD := mono_of_stable hstabD
  refine ⟨?_, ?_⟩
  · intro z v hz hv
    rw [aeval_qpoly_eq_pderiv A z kk, aeval_qpoly_eq_pderiv A _ kk]
    have := hmonoD (Function.update z kk 0) (Function.update v kk 0)
      (fun j => by
        rcases eq_or_ne j kk with rfl | hj
        · simp
        · simpa [hj] using hz j)
      (fun j => by
        rcases eq_or_ne j kk with rfl | hj
        · simp
        · simpa [hj] using hv j)
    have e : Function.update (fun j => z j + (v j : ℂ) * I) kk 0 =
        fun j => Function.update z kk 0 j + ((Function.update v kk 0 j : ℝ) : ℂ) * I := by
      funext j
      rcases eq_or_ne j kk with rfl | hj
      · simp
      · simp [hj]
    rw [e]
    exact this
  · intro x hx
    set g := line (Function.update x kk 0) (Pi.single kk 1) (qpoly A ((kk : ℕ) + 1)) with hgdef
    have hgeval : ∀ u, g.eval u = MvPolynomial.eval (Function.update x kk u)
        (qpoly A ((kk : ℕ) + 1)) := by
      intro u
      rw [hgdef, eval_line_single]
      simp only [Function.update_self, zero_add, Function.update_idem]
      rfl
    have hupd_pos : ∀ u : ℝ, 0 < u → ∀ j, 0 < Function.update x kk u j := by
      intro u hu j
      rcases eq_or_ne j kk with rfl | hj
      · simpa using hu
      · simpa [hj] using hx j
    have hgpos : ∀ u : ℝ, 0 < u → 0 < g.eval u := fun u hu => by
      rw [hgeval]; exact hpos _ (hupd_pos u hu)
    have hreal := roots_im_eq_zero_of_mono hmono (Function.update x kk 0) (Pi.single kk 1)
      (fun j => by
        rcases eq_or_ne j kk with rfl | hj
        · simp
        · simp [hj])
      ⟨1, by
        have := hgpos 1 one_pos
        rw [hgdef, eval_line] at this
        exact this.ne'⟩
    have hfac := real_factor g hreal
    set s := (g.map (algebraMap ℝ ℂ)).roots.map (fun ρ => -ρ.re) with hs
    set c := g.leadingCoeff with hc
    have hsnn : ∀ r ∈ s, 0 ≤ r := by
      intro r hr
      by_contra hneg
      have h0 : g.eval (-r) = 0 := by
        rw [hfac, eval_mul, linProd_eval]
        apply mul_eq_zero_of_right
        apply Multiset.prod_eq_zero
        exact Multiset.mem_map.2 ⟨r, hr, by ring⟩
      exact (hgpos (-r) (by linarith [not_le.1 hneg])).ne' h0
    have hcnn : 0 ≤ c := by
      have h1 := hgpos 1 one_pos
      rw [hfac, eval_mul, eval_C, linProd_eval] at h1
      have hP : 0 < (s.map (fun r => 1 + r)).prod := Multiset.prod_pos (fun a ha => by
        obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 ha; linarith [hsnn r hr])
      exact ((mul_pos_iff_of_pos_right hP).1 h1).le
    have hcard : Multiset.card s ≤ (kk : ℕ) + 1 :=
      (card_real_factor_le g).trans (natDegree_line_qpoly_le A _ kk)
    set M := vdwConst n ((kk : ℕ) + 1) * ∏ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < kk), x j
      with hM
    have hMnn : 0 ≤ M := mul_nonneg (vdwConst_nonneg _ _) (prod_nonneg (fun j _ => (hx j).le))
    have hg : ∀ u : ℝ, 0 < u → M * u ≤ (C c * linProd s).eval u := by
      intro u hu
      rw [← hfac, hgeval]
      have := hcap _ (hupd_pos u hu)
      rw [prod_update_filter] at this
      rw [hM]
      linarith
    have key := univariate_key c s hcnn hsnn ((kk : ℕ) + 1) (by omega) hcard M hMnn hg
    rw [← hfac] at key
    have hd : (derivative g).eval 0 = MvPolynomial.eval x (qpoly A kk) :=
      deriv_line_qpoly A x kk
    rw [hd] at key
    rw [vdwConst_succ kk.2]
    push_cast at key
    simp only [add_sub_cancel_right] at key
    rw [hM] at key
    linarith

theorem gurvitsInv_all (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hpos : ∀ i j, 0 < A i j) : ∀ d k : ℕ, k + d = n → GurvitsInv A k := by
  intro d
  induction d with
  | zero => intro k hk; rw [add_zero] at hk; subst hk; exact gurvitsInv_top A hA
  | succ d ih =>
    intro k hk
    have := ih (k + 1) (by omega)
    exact gurvitsInv_step A hpos ⟨k, by omega⟩ this

/-- **Van der Waerden's bound for positive doubly stochastic matrices.** -/
theorem permanent_ge_of_pos (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hpos : ∀ i j, 0 < A i j) : (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent := by
  have h := (gurvitsInv_all A hA hpos n 0 (zero_add n)).2 (fun _ => 1) (fun _ => one_pos)
  rw [eval_qpoly_zero, vdwConst_zero] at h
  simpa using h

end VdW
