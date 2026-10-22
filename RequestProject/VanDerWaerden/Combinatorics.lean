/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.VanDerWaerden.Stable

/-!
# The polynomials `q_k` of Gurvits's proof

For an `n × n` real matrix `A` and `k ≤ n`, `VdW.qpoly A k` is the polynomial obtained from
`p(x) = ∏ᵢ (A x)ᵢ` by differentiating once in each of the variables `x_k, …, x_{n-1}` and then
setting these variables to zero. Explicitly,
`q_k = ∑_f (∏ᵢ A i (f i)) ∏_{i : f i < k} X (f i)`, the sum running over the maps
`f : Fin n → Fin n` hitting every `j ≥ k` exactly once.

* `VdW.aeval_qpoly_top` : `q_n(z) = ∏ᵢ ∑ⱼ A i j zⱼ`;
* `VdW.eval_qpoly_zero` : `q_0 = per A`;
* `VdW.line_qpoly` : the restriction of `q_{k+1}` to the `k`-th coordinate line;
* `VdW.deriv_line_qpoly` : `q_k(z) = ∂_t q_{k+1}(z with z_k = t)` at `t = 0`.
-/

@[expose] public section

open Finset Polynomial

namespace VdW

variable {n : ℕ}

/-- The maps `f : Fin n → Fin n` hitting every `j ≥ k` exactly once. -/
def admissibleMaps (n k : ℕ) : Finset (Fin n → Fin n) :=
  univ.filter (fun f => ∀ j : Fin n, k ≤ (j : ℕ) → (univ.filter (fun i => f i = j)).card = 1)

/-- The rows sent by `f` to columns `< k`. -/
def low (f : Fin n → Fin n) (k : ℕ) : Finset (Fin n) := univ.filter (fun i => (f i : ℕ) < k)

/-- The rows sent by `f` to the column `j`. -/
def fiber (f : Fin n → Fin n) (j : Fin n) : Finset (Fin n) := univ.filter (fun i => f i = j)

/-- The polynomial `q_k` of Gurvits's proof. -/
noncomputable def qpoly (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ f ∈ admissibleMaps n k, MvPolynomial.C (∏ i, A i (f i)) * ∏ i ∈ low f k, MvPolynomial.X (f i)

lemma card_filter_ge (k : ℕ) : (univ.filter (fun j : Fin n => k ≤ (j : ℕ))).card = n - k := by
  have : (univ.filter (fun j : Fin n => k ≤ (j : ℕ))).map Fin.valEmbedding = Finset.Ico k n := by
    ext m
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨a, h, rfl⟩; exact ⟨h, a.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨m, h2⟩, h1, rfl⟩
  rw [← card_map, this]
  simp

/-- For `f` hitting every `j ≥ k` exactly once, exactly `k` rows go to columns `< k`. -/
lemma card_low {f : Fin n → Fin n} {k : ℕ} (hf : f ∈ admissibleMaps n k) (hk : k ≤ n) :
    (low f k).card = k := by
  simp only [admissibleMaps, mem_filter, mem_univ, true_and] at hf
  have hhigh : (univ.filter (fun i : Fin n => k ≤ (f i : ℕ))).card = n - k := by
    rw [card_eq_sum_card_fiberwise (f := f) (t := univ.filter (fun j : Fin n => k ≤ (j : ℕ)))]
    · rw [← card_filter_ge k, card_eq_sum_ones]
      apply sum_congr rfl
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      rw [← hf j hj]
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨h ▸ hj, h⟩
    · intro i hi
      simpa using hi
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i : Fin n => (f i : ℕ) < k)
  simp only [card_univ, Fintype.card_fin, not_lt] at this
  rw [low]
  omega

lemma admissibleMaps_top : admissibleMaps n n = univ := by
  ext f
  simp only [admissibleMaps, mem_filter, mem_univ, true_and, iff_true]
  intro j hj
  exact absurd j.2 (not_lt.2 hj)

lemma low_top (f : Fin n → Fin n) : low f n = univ := by
  ext i; simp [low]

/-- `q_n(z) = ∏ᵢ (A z)ᵢ`. -/
theorem aeval_qpoly_top {R : Type*} [CommRing R] [Algebra ℝ R] (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → R) :
    MvPolynomial.aeval z (qpoly A n) = ∏ i, ∑ j, algebraMap ℝ R (A i j) * z j := by
  rw [prod_univ_sum, Fintype.piFinset_univ, qpoly, admissibleMaps_top, map_sum]
  apply sum_congr rfl
  intro f _
  rw [low_top]
  simp [prod_mul_distrib]

lemma mem_admissibleMaps_zero_iff (f : Fin n → Fin n) :
    f ∈ admissibleMaps n 0 ↔ Function.Bijective f := by
  simp only [admissibleMaps, mem_filter, mem_univ, true_and, zero_le, forall_const]
  constructor
  · intro h
    have hinj : Function.Injective f := by
      intro a b hab
      obtain ⟨c, hc⟩ := card_eq_one.1 (h (f a))
      have ha : a ∈ univ.filter (fun i => f i = f a) := by simp
      have hb : b ∈ univ.filter (fun i => f i = f a) := by simp [hab]
      rw [hc] at ha hb
      simp only [mem_singleton] at ha hb
      rw [ha, hb]
    exact Finite.injective_iff_bijective.1 hinj
  · intro h j
    obtain ⟨a, ha⟩ := h.2 j
    rw [card_eq_one]
    refine ⟨a, ?_⟩
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hi; exact h.1 (hi.trans ha.symm)
    · rintro rfl; exact ha

/-- `q_0 = per A`. -/
theorem eval_qpoly_zero (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (qpoly A 0) = A.permanent := by
  rw [← Matrix.permanent_transpose, Matrix.permanent, qpoly, map_sum]
  have hlow : ∀ f : Fin n → Fin n, low f 0 = ∅ := fun f => by ext i; simp [low]
  simp only [hlow, prod_empty, mul_one, MvPolynomial.eval_C, Matrix.transpose_apply]
  symm
  refine sum_bij (fun σ _ => ⇑σ) (fun σ _ => ?_) (fun σ _ τ _ h => ?_) (fun f hf => ?_)
    (fun σ _ => rfl)
  · exact (mem_admissibleMaps_zero_iff _).2 σ.bijective
  · exact DFunLike.coe_injective h
  · exact ⟨Equiv.ofBijective f ((mem_admissibleMaps_zero_iff f).1 hf), mem_univ _, rfl⟩

lemma low_succ_eq (f : Fin n → Fin n) (kk : Fin n) :
    low f ((kk : ℕ) + 1) = low f kk ∪ fiber f kk := by
  ext i
  simp only [low, fiber, mem_union, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (Fin.ext h)
  · rintro (h | rfl) <;> omega

lemma disjoint_low_fiber (f : Fin n → Fin n) (kk : Fin n) : Disjoint (low f kk) (fiber f kk) := by
  rw [disjoint_left]
  intro i h1 h2
  simp only [low, fiber, mem_filter, mem_univ, true_and] at h1 h2
  rw [h2] at h1
  exact lt_irrefl _ h1

/-- The restriction of `q_{k+1}` to the `k`-th coordinate line through `z` (with `z_k = 0`). -/
theorem line_qpoly {R : Type*} [CommRing R] [Algebra ℝ R] (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → R) (kk : Fin n) :
    line (Function.update z kk 0) (Pi.single kk 1) (qpoly A ((kk : ℕ) + 1)) =
      ∑ f ∈ admissibleMaps n ((kk : ℕ) + 1),
        C (algebraMap ℝ R (∏ i, A i (f i)) * ∏ i ∈ low f kk, z (f i)) * X ^ (fiber f kk).card := by
  unfold line qpoly
  rw [map_sum]
  apply sum_congr rfl
  intro f _
  rw [map_mul, low_succ_eq, prod_union (disjoint_low_fiber f kk), map_mul]
  have h1 : (MvPolynomial.aeval (fun j => C (Function.update z kk 0 j) +
      C ((Pi.single kk (1 : R) : Fin n → R) j) * X))
      (∏ i ∈ low f kk, (MvPolynomial.X (f i) : MvPolynomial (Fin n) ℝ)) =
      ∏ i ∈ low f kk, C (z (f i)) := by
    rw [map_prod]
    apply prod_congr rfl
    intro i hi
    have hne : f i ≠ kk := by
      intro h
      simp only [low, mem_filter, mem_univ, true_and] at hi
      rw [h] at hi
      exact lt_irrefl _ hi
    simp [hne]
  have h2 : (MvPolynomial.aeval (fun j => C (Function.update z kk 0 j) +
      C ((Pi.single kk (1 : R) : Fin n → R) j) * X))
      (∏ i ∈ fiber f kk, (MvPolynomial.X (f i) : MvPolynomial (Fin n) ℝ)) =
      X ^ (fiber f kk).card := by
    rw [map_prod, ← prod_const]
    apply prod_congr rfl
    intro i hi
    simp only [fiber, mem_filter, mem_univ, true_and] at hi
    simp [hi]
  rw [h1, h2, MvPolynomial.aeval_C, C_mul, ← map_prod C, Polynomial.algebraMap_apply]
  ring

lemma eval_zero_derivative_C_mul_X_pow {R : Type*} [CommRing R] (a : R) (m : ℕ) :
    (derivative (C a * X ^ m)).eval 0 = if m = 1 then a else 0 := by
  rw [derivative_C_mul_X_pow]
  rcases m with _ | _ | m
  · simp
  · simp
  · simp

lemma admissibleMaps_succ_filter (kk : Fin n) :
    (admissibleMaps n ((kk : ℕ) + 1)).filter (fun f => (fiber f kk).card = 1) =
      admissibleMaps n kk := by
  ext f
  rw [mem_filter]
  simp only [admissibleMaps, fiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, hk⟩ j hj
    rcases Nat.lt_or_ge (j : ℕ) ((kk : ℕ) + 1) with h' | h'
    · have : j = kk := Fin.ext (by omega)
      rw [this]; exact hk
    · exact h j h'
  · intro h
    exact ⟨fun j hj => h j (by omega), h kk le_rfl⟩

/-- `q_k(z) = ∂_t q_{k+1}(z₀, …, z_{k-1}, t, …)` at `t = 0`. -/
theorem deriv_line_qpoly {R : Type*} [CommRing R] [Algebra ℝ R] (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → R) (kk : Fin n) :
    (derivative (line (Function.update z kk 0) (Pi.single kk 1) (qpoly A ((kk : ℕ) + 1)))).eval 0
      = MvPolynomial.aeval z (qpoly A kk) := by
  rw [line_qpoly, derivative_sum, eval_finsetSum]
  simp only [eval_zero_derivative_C_mul_X_pow]
  rw [← sum_filter, admissibleMaps_succ_filter, qpoly, map_sum]
  apply sum_congr rfl
  intro f _
  simp [map_prod]

/-- `q_k(z) = (∂_k q_{k+1})(z with z_k = 0)`. -/
theorem aeval_qpoly_eq_pderiv {R : Type*} [CommRing R] [Algebra ℝ R]
    (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → R) (kk : Fin n) :
    MvPolynomial.aeval z (qpoly A kk) = MvPolynomial.aeval (Function.update z kk 0)
      (MvPolynomial.pderiv kk (qpoly A ((kk : ℕ) + 1))) := by
  rw [← deriv_line_qpoly, line_derivative, eval_line_single]
  simp

lemma card_filter_lt {k : ℕ} (hk : k ≤ n) :
    (univ.filter (fun j : Fin n => (j : ℕ) < k)).card = k := by
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun j : Fin n => (j : ℕ) < k)
  have h2 := card_filter_ge (n := n) k
  simp only [card_univ, Fintype.card_fin, not_lt] at h1
  omega

lemma fiber_subset_low_succ (f : Fin n → Fin n) (kk : Fin n) :
    fiber f kk ⊆ low f ((kk : ℕ) + 1) := by
  rw [low_succ_eq]; exact subset_union_right

lemma card_fiber_le {f : Fin n → Fin n} {kk : Fin n} (hf : f ∈ admissibleMaps n ((kk : ℕ) + 1))
    (hk : (kk : ℕ) + 1 ≤ n) : (fiber f kk).card ≤ (kk : ℕ) + 1 := by
  rw [← card_low hf hk]
  exact card_le_card (fiber_subset_low_succ f kk)

lemma low_eq_empty_of_card_fiber {f : Fin n → Fin n} {kk : Fin n}
    (hf : f ∈ admissibleMaps n ((kk : ℕ) + 1)) (hk : (kk : ℕ) + 1 ≤ n)
    (hm : (fiber f kk).card = (kk : ℕ) + 1) : low f kk = ∅ := by
  have h := card_low hf hk
  rw [low_succ_eq, card_union_of_disjoint (disjoint_low_fiber f kk), hm] at h
  exact card_eq_zero.1 (by omega)

/-- The restriction of `q_{k+1}` to the `k`-th coordinate line has degree at most `k + 1`. -/
theorem natDegree_line_qpoly_le {R : Type*} [CommRing R] [Algebra ℝ R]
    (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → R) (kk : Fin n) :
    (line (Function.update z kk 0) (Pi.single kk 1) (qpoly A ((kk : ℕ) + 1))).natDegree ≤
      (kk : ℕ) + 1 := by
  rw [line_qpoly]
  apply natDegree_sum_le_of_forall_le
  intro f hf
  calc _ ≤ (fiber f kk).card := natDegree_C_mul_X_pow_le _ _
    _ ≤ _ := card_fiber_le hf kk.2

/-- The map sending the rows `0, …, k` to the column `k` and fixing the other rows. -/
def topMap (kk : Fin n) : Fin n → Fin n := fun i => if (i : ℕ) ≤ kk then kk else i

lemma topMap_mem (kk : Fin n) : topMap kk ∈ admissibleMaps n ((kk : ℕ) + 1) := by
  simp only [admissibleMaps, mem_filter, mem_univ, true_and]
  intro j hj
  rw [card_eq_one]
  refine ⟨j, ?_⟩
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  unfold topMap
  constructor
  · intro h
    split_ifs at h with hi
    · exact absurd (h ▸ hj) (by omega)
    · exact h
  · rintro rfl
    rw [ite_eq_right (by omega)]

lemma card_fiber_topMap (kk : Fin n) : (fiber (topMap kk) kk).card = (kk : ℕ) + 1 := by
  have : fiber (topMap kk) kk = univ.filter (fun j : Fin n => (j : ℕ) < (kk : ℕ) + 1) := by
    ext i
    simp only [fiber, mem_filter, mem_univ, true_and]
    unfold topMap
    constructor
    · intro h
      split_ifs at h with hi
      · omega
      · rw [h] at hi; omega
    · intro h
      rw [ite_eq_left (by omega)]
  rw [this, card_filter_lt kk.2]

/-- For a positive matrix, the restriction of `q_{k+1}` to the `k`-th coordinate line is
nonconstant. -/
theorem degree_line_qpoly_pos (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
    (z : Fin n → ℂ) (kk : Fin n) :
    0 < (line (Function.update z kk 0) (Pi.single kk 1) (qpoly A ((kk : ℕ) + 1))).degree := by
  have hcoeff : (line (Function.update z kk 0) (Pi.single kk 1)
      (qpoly A ((kk : ℕ) + 1))).coeff ((kk : ℕ) + 1) =
      ((∑ f ∈ (admissibleMaps n ((kk : ℕ) + 1)).filter
        (fun f => (fiber f kk).card = (kk : ℕ) + 1), ∏ i, A i (f i) : ℝ) : ℂ) := by
    rw [line_qpoly, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Complex.ofReal_sum, sum_filter]
    apply sum_congr rfl
    intro f hf
    by_cases hm : (fiber f kk).card = (kk : ℕ) + 1
    · rw [ite_eq_left hm.symm, ite_eq_left hm, low_eq_empty_of_card_fiber hf kk.2 hm]
      simp
    · rw [ite_eq_right (Ne.symm hm), ite_eq_right hm]
  have hpos : 0 < ∑ f ∈ (admissibleMaps n ((kk : ℕ) + 1)).filter
      (fun f => (fiber f kk).card = (kk : ℕ) + 1), ∏ i, A i (f i) := by
    apply sum_pos (fun f _ => prod_pos (fun i _ => hA _ _))
    exact ⟨topMap kk, mem_filter.2 ⟨topMap_mem kk, card_fiber_topMap kk⟩⟩
  have hne : (line (Function.update z kk 0) (Pi.single kk 1)
      (qpoly A ((kk : ℕ) + 1))).coeff ((kk : ℕ) + 1) ≠ 0 := by
    rw [hcoeff]; exact_mod_cast hpos.ne'
  have := le_degree_of_ne_zero hne
  exact lt_of_lt_of_le (by exact_mod_cast Nat.succ_pos _) this

end VdW
