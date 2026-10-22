/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Hall

/-!
# Section 3 of the paper: Latin squares

* `STS.theoremA` : `L(n) ≥ n! (n-1)! ⋯ 1!`.
* `STS.theoremB` : if the vdWPC holds, `L(n) ≥ (n!)^{2n} / n^{n²}`.
* `STS.lemma2`, `STS.lemma2_vdW` : Lemma 2, inequalities (3.1) and (3.2).

The proofs count Latin rectangles row by row: a `k × n` Latin rectangle can be extended by a
new row in as many ways as the family of sets of available symbols in each column has
systems of distinct representatives. M. Hall's theorem gives at least `(n-k)!` of them, and
the vdWPC gives at least `(n-k)^n n!/n^n` of them (this number is the permanent of a 0-1 matrix
with all line sums `n - k`).
-/

@[expose] public section

open Finset

namespace STS

/-- Latin rectangles with `k` rows and `n` columns (rows are permutations of the symbols, and
the entries of each column are distinct). -/
def LR (n k : ℕ) : Type :=
  {r : Fin k → Equiv.Perm (Fin n) // ∀ i j, i ≠ j → ∀ c, r i c ≠ r j c}

noncomputable instance (n k : ℕ) : Fintype (LR n k) := by unfold LR; infer_instance

/-- The symbols still available in column `c`. -/
def avail {n k : ℕ} (r : Fin k → Equiv.Perm (Fin n)) (c : Fin n) : Finset (Fin n) :=
  univ.filter (fun s => ∀ i, r i c ≠ s)

/-- The admissible new rows. -/
def extRows {n k : ℕ} (r : Fin k → Equiv.Perm (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter (fun p => ∀ c, p c ∈ avail r c)

lemma card_LR_succ_ge (n k : ℕ) :
    ∑ r : LR n k, (extRows r.1).card ≤ Fintype.card (LR n (k + 1)) := by
  classical
  let f : (Σ r : LR n k, extRows r.1) → LR n (k + 1) := fun p =>
    ⟨Fin.snoc (α := fun _ => Equiv.Perm (Fin n)) p.1.1 p.2.1, by
      intro i j hij c
      have hp := p.2.2
      simp only [extRows, avail, mem_filter, mem_univ, true_and] at hp
      revert hij
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
        intro hij
      · exact absurd rfl hij
      · simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact (hp c j').symm
      · simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact hp c i'
      · simp only [Fin.snoc_castSucc]
        exact p.1.2 i' j' (fun h => hij (by rw [h])) c⟩
  have hf : Function.Injective f := by
    rintro ⟨r₁, p₁⟩ ⟨r₂, p₂⟩ h
    have h' := congrArg Subtype.val h
    simp only [f] at h'
    have hr : r₁ = r₂ := Subtype.ext (by
      funext i; have := congrFun h' (Fin.castSucc i); simpa using this)
    subst hr
    have hp : p₁ = p₂ := Subtype.ext (by
      have := congrFun h' (Fin.last k); simpa using this)
    subst hp; rfl
  have := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at this
  simpa using this

lemma avail_card {n k : ℕ} (r : LR n k) (c : Fin n) : (avail r.1 c).card = n - k := by
  have himg : (univ.image (fun i => r.1 i c)).card = k := by
    rw [card_image_of_injective _ (fun i j h => by
      by_contra hij; exact r.2 i j hij c h), card_univ, Fintype.card_fin]
  have : avail r.1 c = univ \ univ.image (fun i => r.1 i c) := by
    ext s; simp [avail]
  rw [this, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, himg]

lemma symbol_count {n k : ℕ} (r : LR n k) (s : Fin n) :
    (univ.filter (fun c => s ∈ avail r.1 c)).card = n - k := by
  have himg : (univ.image (fun i => (r.1 i).symm s)).card = k := by
    rw [card_image_of_injective _ (fun i j h => by
      by_contra hij
      apply r.2 i j hij ((r.1 i).symm s)
      conv_rhs => rw [h]
      simp), card_univ, Fintype.card_fin]
  have : univ.filter (fun c => s ∈ avail r.1 c) = univ \ univ.image (fun i => (r.1 i).symm s) := by
    ext c
    simp only [avail, mem_filter, mem_univ, true_and, mem_sdiff, mem_image, not_exists]
    constructor
    · intro h i hi; exact h i (by rw [← hi]; simp)
    · intro h i hi; exact h i (by rw [← hi]; simp)
  rw [this, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, himg]

lemma hall_avail {n k : ℕ} (r : LR n k) (hk : k < n) (S : Finset (Fin n)) :
    S.card ≤ (S.biUnion (avail r.1)).card := by
  set U := S.biUnion (avail r.1)
  have h1 : ∑ c ∈ S, (avail r.1 c).card = ∑ s ∈ U, (S.filter (fun c => s ∈ avail r.1 c)).card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro c hc
    rw [← sum_filter]
    congr 1
    ext s
    simp only [mem_filter, U, mem_biUnion]
    constructor
    · intro h; exact ⟨⟨c, hc, h⟩, h⟩
    · intro h; exact h.2
  have h2 : ∑ s ∈ U, (S.filter (fun c => s ∈ avail r.1 c)).card ≤ U.card * (n - k) := by
    rw [← smul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro s _
    rw [← symbol_count r s]
    exact card_le_card (filter_subset_filter _ (subset_univ _))
  rw [sum_congr rfl (fun c _ => avail_card r c), sum_const, smul_eq_mul] at h1
  have := h1.symm ▸ h2
  exact Nat.le_of_mul_le_mul_right this (by omega)

lemma extRows_card_eq {n k : ℕ} (r : LR n k) :
    (extRows r.1).card = Nat.card {f : Fin n → Fin n // Function.Injective f ∧
      ∀ c, f c ∈ avail r.1 c} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine card_bij (fun p _ => ⇑p) ?_ ?_ ?_
  · intro p hp
    simp only [extRows, mem_filter, mem_univ, true_and] at hp
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨p.injective, hp⟩
  · intro p _ q _ h; exact Equiv.ext (congrFun h)
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf.1), ?_, rfl⟩
    simp only [extRows, mem_filter, mem_univ, true_and]
    exact hf.2

lemma extRows_card_ge {n k : ℕ} (r : LR n k) (hk : k < n) :
    (n - k).factorial ≤ (extRows r.1).card := by
  rw [extRows_card_eq]
  exact hall_sdr_count (avail r.1) (n - k) (by simp) (hall_avail r hk)
    (fun c => (avail_card r c).ge)

lemma LR_card_ge (n : ℕ) : ∀ k, k ≤ n →
    ∏ i ∈ range k, (n - i).factorial ≤ Fintype.card (LR n k) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [range_zero, prod_empty]
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Fintype.card_pos_iff]
    exact ⟨⟨Fin.elim0, fun i => i.elim0⟩⟩
  | succ k ih =>
    intro hk
    rw [prod_range_succ]
    calc (∏ i ∈ range k, (n - i).factorial) * (n - k).factorial
        ≤ Fintype.card (LR n k) * (n - k).factorial :=
          Nat.mul_le_mul_right _ (ih (by omega))
      _ = ∑ _r : LR n k, (n - k).factorial := by rw [sum_const, card_univ, smul_eq_mul]
      _ ≤ ∑ r : LR n k, (extRows r.1).card :=
          sum_le_sum (fun r _ => extRows_card_ge r (by omega))
      _ ≤ _ := card_LR_succ_ge n k

lemma LR_le_L (n : ℕ) : Fintype.card (LR n n) ≤ L n := by
  classical
  rw [L, Nat.card_eq_fintype_card]
  refine Fintype.card_le_of_injective (fun r => ⟨fun i c => r.1 i c, fun i => (r.1 i).bijective,
    fun c => Finite.injective_iff_bijective.1 (fun i j h => by
      by_contra hij; exact r.2 i j hij c h)⟩) ?_
  intro r₁ r₂ h
  apply Subtype.ext
  funext i
  apply Equiv.ext
  intro c
  have := congrArg Subtype.val h
  exact congrFun (congrFun this i) c

/-- **Theorem A.** `L(n) ≥ n! (n-1)! ⋯ 2! 1!`. -/
theorem theoremA (n : ℕ) : ∏ i ∈ Finset.range n, (i + 1).factorial ≤ L n := by
  have h := LR_card_ge n n le_rfl
  rw [← prod_range_reflect] at h
  have : ∏ j ∈ range n, (n - (n - 1 - j)).factorial = ∏ i ∈ range n, (i + 1).factorial := by
    apply prod_congr rfl
    intro j hj
    rw [mem_range] at hj
    congr 1; omega
  rw [this] at h
  exact h.trans (LR_le_L n)

/-! ### Theorem B -/

lemma extRows_card_ge_vdW (h : vdWPC) {n k : ℕ} (r : LR n k) (hk : k < n) :
    ((n - k : ℕ) : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤ (extRows r.1).card := by
  classical
  set m : ℝ := ((n - k : ℕ) : ℝ) with hm
  have hm0 : 0 < m := by rw [hm]; exact_mod_cast (show 0 < n - k by omega)
  let M : Matrix (Fin n) (Fin n) ℝ := fun s c => if s ∈ avail r.1 c then 1 else 0
  have hper : M.permanent = (extRows r.1).card := by
    rw [Matrix.permanent]
    simp only [M, Finset.prod_boole, Finset.mem_univ, true_implies, Finset.sum_boole]
    rfl
  have hM : ∀ s c, (m⁻¹ • M) s c = m⁻¹ * (if s ∈ avail r.1 c then 1 else 0) := fun s c => rfl
  have hds : m⁻¹ • M ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun s c => ?_, fun s => ?_, fun c => ?_⟩
    · rw [hM]
      split_ifs <;> positivity
    · simp only [hM, ← Finset.mul_sum]
      rw [Finset.sum_boole, symbol_count r s, ← hm, inv_mul_cancel₀ hm0.ne']
    · simp only [hM, ← Finset.mul_sum]
      rw [Finset.sum_boole]
      have : (univ.filter (fun s => s ∈ avail r.1 c)) = avail r.1 c := by simp
      rw [this, avail_card r c, ← hm, inv_mul_cancel₀ hm0.ne']
  have := h n _ hds
  rw [Matrix.permanent_smul, Fintype.card_fin, hper] at this
  have hmn : 0 < m ^ n := pow_pos hm0 n
  calc m ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤ m ^ n * (m⁻¹ ^ n * (extRows r.1).card) :=
        mul_le_mul_of_nonneg_left this hmn.le
    _ = (extRows r.1).card := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hm0.ne', one_pow, one_mul]

lemma LR_card_ge_vdW (h : vdWPC) (n : ℕ) : ∀ k, k ≤ n →
    ∏ i ∈ range k, (((n - i : ℕ) : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n)) ≤
      Fintype.card (LR n k) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [range_zero, prod_empty, Nat.one_le_cast]
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Fintype.card_pos_iff]
    exact ⟨⟨Fin.elim0, fun i => i.elim0⟩⟩
  | succ k ih =>
    intro hk
    rw [prod_range_succ]
    have hc : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n) := by positivity
    calc (∏ i ∈ range k, (((n - i : ℕ) : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n))) *
          (((n - k : ℕ) : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n))
        ≤ Fintype.card (LR n k) * (((n - k : ℕ) : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n)) :=
          mul_le_mul_of_nonneg_right (ih (by omega)) hc
      _ = ∑ _r : LR n k, (((n - k : ℕ) : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n)) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ ∑ r : LR n k, ((extRows r.1).card : ℝ) :=
          sum_le_sum (fun r _ => extRows_card_ge_vdW h r (by omega))
      _ ≤ _ := by exact_mod_cast card_LR_succ_ge n k

/-- **Theorem B.** If the van der Waerden permanent conjecture is valid, then
`L(n) ≥ (n!)^{2n} / n^{n²}`. -/
theorem theoremB (h : vdWPC) (n : ℕ) :
    ((n.factorial : ℝ) ^ (2 * n)) / (n : ℝ) ^ (n ^ 2) ≤ L n := by
  have h1 := LR_card_ge_vdW h n n le_rfl
  have h2 : (Fintype.card (LR n n) : ℝ) ≤ L n := by exact_mod_cast LR_le_L n
  refine le_trans (le_of_eq ?_) (h1.trans h2)
  rw [prod_mul_distrib, prod_const, card_range, prod_pow]
  have : ∏ i ∈ range n, ((n - i : ℕ) : ℝ) = (n.factorial : ℝ) := by
    rw [← prod_range_reflect]
    have : ∏ j ∈ range n, ((n - (n - 1 - j) : ℕ) : ℝ) = ∏ j ∈ range n, ((j + 1 : ℕ) : ℝ) := by
      apply prod_congr rfl
      intro j hj; rw [mem_range] at hj; congr 2; omega
    rw [this, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  rw [this, div_pow, ← pow_mul]
  rw [show 2 * n = n + n by ring, pow_add, show n ^ 2 = n * n by ring, mul_div_assoc]

/-! ### Lemma 2 -/

lemma log_factorial_ge (m : ℕ) : (m : ℝ) * Real.log m - m ≤ Real.log (m.factorial) := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; simp
  have h := Real.pow_div_factorial_le_exp (x := (m : ℝ)) (by positivity) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hm : (0 : ℝ) < m := by exact_mod_cast h0
  rw [div_le_iff₀ hf] at h
  have := Real.log_le_log (by positivity) h
  rw [Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp, Real.log_pow] at this
  linarith

lemma sum_mlogm_ge (n : ℕ) :
    (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 ≤
      ∑ i ∈ range n, (((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hkey : (n : ℝ) ^ 2 * (Real.log (n + 1) - Real.log n) ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp
      have hn : (0 : ℝ) < n := by exact_mod_cast h0
      have : Real.log (n + 1) - Real.log n ≤ 1 / n := by
        rw [← Real.log_div (by positivity) hn.ne']
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (n + 1) / n by positivity)
        rw [show ((n : ℝ) + 1) / n - 1 = 1 / n by field_simp; ring] at this
        exact this
      calc (n : ℝ) ^ 2 * (Real.log (n + 1) - Real.log n) ≤ (n : ℝ) ^ 2 * (1 / n) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = n := by field_simp
    have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
    push_cast at ih ⊢
    nlinarith

/-- **Lemma 2**, inequality (3.1): `L(n) ≥ (e^{-2} n)^{n²/2}`. -/
theorem lemma2 (n : ℕ) : (Real.exp (-2) * n) ^ ((n : ℝ) ^ 2 / 2) ≤ L n := by
  have hA : (∏ i ∈ Finset.range n, (i + 1).factorial : ℝ) ≤ L n := by exact_mod_cast theoremA n
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp only [Nat.cast_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_div, Real.rpow_zero]
    simpa using hA
  have hn : (0 : ℝ) < n := by exact_mod_cast h0
  have hpos : (0 : ℝ) < ∏ i ∈ Finset.range n, ((i + 1).factorial : ℝ) := by
    apply prod_pos; intro i _; exact_mod_cast Nat.factorial_pos _
  have hbase : 0 < Real.exp (-2) * n := by positivity
  refine le_trans ?_ hA
  rw [← Real.exp_log hpos, ← Real.exp_log (Real.rpow_pos_of_pos hbase _)]
  apply Real.exp_le_exp.2
  rw [Real.log_rpow hbase, Real.log_mul (Real.exp_pos _).ne' hn.ne', Real.log_exp,
    Real.log_prod (fun i _ => by positivity)]
  have h1 := sum_mlogm_ge n
  have h2 : ∑ i ∈ range n, (((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) ≤
      ∑ i ∈ range n, Real.log (((i + 1).factorial : ℕ) : ℝ) :=
    sum_le_sum (fun i _ => log_factorial_ge (i + 1))
  push_cast at h1 h2 ⊢
  have : (n : ℝ) ^ 2 / 2 * (-2 + Real.log n) = (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 := by
    ring
  linarith

/-- **Lemma 2**, inequality (3.2): if the vdWPC is valid, `L(n) ≥ (e^{-2} n)^{n²}`. -/
theorem lemma2_vdW (h : vdWPC) (n : ℕ) : (Real.exp (-2) * n) ^ (n ^ 2) ≤ L n := by
  refine le_trans ?_ (theoremB h n)
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp
  have hn : (0 : ℝ) < n := by exact_mod_cast h0
  have hfac : ((n : ℝ) / Real.exp 1) ^ n ≤ n.factorial := by
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hn.le n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    rw [div_pow, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hf] at h
    rw [← Real.exp_nat_mul, mul_one] at *
    linarith [mul_comm (Real.exp n) (n.factorial : ℝ)]
  rw [le_div_iff₀ (by positivity)]
  calc (Real.exp (-2) * n) ^ (n ^ 2) * (n : ℝ) ^ (n ^ 2) = (((n : ℝ) / Real.exp 1) ^ n) ^ (2 * n) := by
        have he2 : Real.exp (-2) = (Real.exp 1 ^ 2)⁻¹ := by
          rw [Real.exp_neg, Real.exp_one_pow]; norm_num
        rw [he2, ← pow_mul, div_pow, mul_pow, inv_pow, ← pow_mul]
        rw [show n * (2 * n) = 2 * n ^ 2 by ring, show 2 * n ^ 2 = n ^ 2 + n ^ 2 by ring, pow_add]
        field_simp
        rw [pow_add]; ring
    _ ≤ (n.factorial : ℝ) ^ (2 * n) := pow_le_pow_left₀ (by positivity) hfac _

end STS
