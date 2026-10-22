/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Basic

/-!
# Section 2 of the paper: an upper bound for `N(v)`

* `STS.N_le_D`, `STS.D_le_factorial_mul_N` : inequality (2.1).
* `STS.triangles E` : the triangles of a simple graph given by its set `E` of 2-subsets.
* `STS.lemma1` : Lemma 1 (number of triangles in a graph with `q` edges).
* `STS.triangles_le_sqrt` : the bound `(√2/3) q^{3/2}` used in the proof of Theorem 1.
* `STS.theorem1` : Theorem 1, `N(v) < (e^{-1/2} v)^{v²/6}` for `v ≥ 7`.
-/

@[expose] public section

open Finset

namespace STS

/-- Inequality (2.1), left half: `N(v) ≤ D(v)`. -/
theorem N_le_D (v : ℕ) : N v ≤ D v := N_le_D' v

/-- Inequality (2.1), right half: `D(v) ≤ v! N(v)`. -/
theorem D_le_factorial_mul_N (v : ℕ) : D v ≤ v.factorial * N v := D_le_factorial_mul_N' v


lemma sum_card_filter_mem {X : Type*} [Fintype X] [DecidableEq X] (S : Finset (Finset X)) :
    ∑ w, (S.filter (w ∈ ·)).card = ∑ e ∈ S, e.card := by
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp

/-- The triangles of the simple graph `(X, E)` (where `E` is a set of 2-subsets of `X`): the
3-subsets `A ⊆ X` all of whose 2-subsets belong to `E`. -/
def triangles {X : Type*} [Fintype X] [DecidableEq X] (E : Finset (Finset X)) :
    Finset (Finset X) :=
  (univ.powersetCard 3).filter (fun A => A.powersetCard 2 ⊆ E)

variable {X : Type*} [Fintype X] [DecidableEq X]

lemma tri_w_le_E (E : Finset (Finset X)) (w : X) :
    ((triangles E).filter (w ∈ ·)).card ≤ E.card := by
  refine card_le_card_of_injOn (fun A => A.erase w) ?_ ?_
  · intro A hA
    simp only [triangles, coe_filter, mem_filter, mem_powersetCard, subset_univ, true_and,
      Set.mem_setOf_eq] at hA
    apply hA.1.2
    rw [mem_powersetCard]
    exact ⟨erase_subset _ _, by rw [card_erase_of_mem hA.2, hA.1.1]⟩
  · intro A hA B hB h
    simp only [coe_filter, Set.mem_setOf_eq] at hA hB
    have := congrArg (insert w) h
    simpa [insert_erase hA.2, insert_erase hB.2] using this

lemma tri_w_le_choose (E : Finset (Finset X)) (hE : ∀ e ∈ E, e.card = 2) (w : X) :
    ((triangles E).filter (w ∈ ·)).card ≤ ((E.filter (w ∈ ·)).card).choose 2 := by
  set Nb := univ.filter (fun x => x ≠ w ∧ ({w, x} : Finset X) ∈ E)
  have hNb : Nb.card ≤ (E.filter (w ∈ ·)).card := by
    refine card_le_card_of_injOn (fun x => ({w, x} : Finset X)) ?_ ?_
    · intro x hx
      simp only [Nb, coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx
      simp [hx.2]
    · intro x hx y hy h
      simp only [Nb, coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq] at hx hy
      have : x ∈ ({w, y} : Finset X) := by
        simp only at h; rw [← h]; simp
      simp at this
      rcases this with h1 | h1
      · exact absurd h1 hx.1
      · exact h1
  refine le_trans ?_ (Nat.choose_le_choose 2 hNb)
  rw [← card_powersetCard]
  refine card_le_card_of_injOn (fun A => A.erase w) ?_ ?_
  · intro A hA
    simp only [triangles, coe_filter, mem_filter, mem_powersetCard, subset_univ, true_and,
      Set.mem_setOf_eq] at hA
    rw [Finset.mem_coe, mem_powersetCard]
    refine ⟨?_, by rw [card_erase_of_mem hA.2, hA.1.1]⟩
    intro x hx
    have hxw := ne_of_mem_erase hx
    have hxA := mem_of_mem_erase hx
    simp only [Nb, mem_filter, mem_univ, true_and]
    refine ⟨hxw, hA.1.2 ?_⟩
    rw [mem_powersetCard]
    refine ⟨?_, card_pair (Ne.symm hxw)⟩
    intro y hy
    simp at hy
    rcases hy with rfl | rfl
    · exact hA.2
    · exact hxA
  · intro A hA B hB h
    simp only [coe_filter, Set.mem_setOf_eq] at hA hB
    have := congrArg (insert w) h
    simpa [insert_erase hA.2, insert_erase hB.2] using this

lemma min_le_sqrt (d q : ℝ) (hd : 0 ≤ d) (hq : 0 ≤ q) :
    min (d ^ 2 / 2) q ≤ d * Real.sqrt (q / 2) := by
  rcases le_or_gt d (Real.sqrt (2 * q)) with h | h
  · refine (min_le_left _ _).trans ?_
    have : Real.sqrt (2*q) = 2 * Real.sqrt (q/2) := by
      rw [show 2*q = 2^2 * (q/2) by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    nlinarith [Real.sqrt_nonneg (q/2)]
  · refine (min_le_right _ _).trans ?_
    have h1 : Real.sqrt (2*q) * Real.sqrt (q/2) = q := by
      rw [← Real.sqrt_mul (by positivity)]; rw [show 2*q*(q/2) = q^2 by ring, Real.sqrt_sq hq]
    nlinarith [Real.sqrt_nonneg (q/2)]

/-- A simple graph `(X, E)` with `q = |E|` edges has at most `(√2/3) q^{3/2}` triangles (this is
the form of Lemma 1 used in the proof of Theorem 1). -/
theorem triangles_le_sqrt (E : Finset (Finset X)) (hE : ∀ e ∈ E, e.card = 2) :
    ((triangles E).card : ℝ) ≤ Real.sqrt 2 / 3 * (E.card : ℝ) ^ (3 / 2 : ℝ) := by
  have h3 : 3 * (triangles E).card = ∑ w, ((triangles E).filter (w ∈ ·)).card := by
    rw [sum_card_filter_mem, sum_const_nat (m := 3)]
    · ring
    · intro A hA
      simp only [triangles, mem_filter, mem_powersetCard] at hA
      exact hA.1.2
  have h2 : ∑ w, (E.filter (w ∈ ·)).card = 2 * E.card := by
    rw [sum_card_filter_mem, sum_const_nat (m := 2) hE]; ring
  have key : ∀ w, (((triangles E).filter (w ∈ ·)).card : ℝ) ≤
      ((E.filter (w ∈ ·)).card : ℝ) * Real.sqrt ((E.card : ℝ) / 2) := by
    intro w
    refine le_trans ?_ (min_le_sqrt _ _ (by positivity) (by positivity))
    refine le_min ?_ (by exact_mod_cast tri_w_le_E E w)
    have := tri_w_le_choose E hE w
    have h' : ((((E.filter (w ∈ ·)).card).choose 2 : ℕ) : ℝ) ≤
        ((E.filter (w ∈ ·)).card : ℝ) ^ 2 / 2 := by
      rw [Nat.cast_choose_two]
      have : (0:ℝ) ≤ ((E.filter (w ∈ ·)).card : ℝ) := by positivity
      nlinarith
    exact le_trans (by exact_mod_cast this) h'
  have hsum : (3 * (triangles E).card : ℝ) ≤ 2 * (E.card : ℝ) * Real.sqrt ((E.card : ℝ) / 2) := by
    have := Finset.sum_le_sum (fun w (_ : w ∈ (univ : Finset X)) => key w)
    rw [← sum_mul] at this
    have e1 : ((3 * (triangles E).card : ℕ) : ℝ) = (3 * (triangles E).card : ℝ) := by push_cast; ring
    have e2 : ((2 * E.card : ℕ) : ℝ) = (2 * E.card : ℝ) := by push_cast; ring
    rw [← e1, h3, ← e2, ← h2]
    push_cast
    exact this
  have hq0 : (0:ℝ) ≤ E.card := by positivity
  have hpow : (E.card : ℝ) ^ (3 / 2 : ℝ) = E.card * Real.sqrt E.card := by
    rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add' hq0 (by norm_num), Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [hpow]
  have : Real.sqrt ((E.card : ℝ) / 2) = Real.sqrt E.card / Real.sqrt 2 :=
    Real.sqrt_div' _ (by norm_num)
  rw [this] at hsum
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2p : 0 < Real.sqrt 2 := by positivity
  rw [mul_div_assoc', le_div_iff₀ hs2p] at hsum
  nlinarith

/-! ### Counting blocks -/

section blocks

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Two distinct blocks of an STS share at most one point. -/
lemma inter_card_le_one {B : Finset (Finset Y)} (hB : IsSTS B) {A A' : Finset Y} (hA : A ∈ B)
    (hA' : A' ∈ B) (hne : A ≠ A') : (A ∩ A').card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h
  obtain ⟨C, _, hC⟩ := hB.2 x y hxy
  have h1 := hC A ⟨hA, (mem_inter.1 hx).1, (mem_inter.1 hy).1⟩
  have h2 := hC A' ⟨hA', (mem_inter.1 hx).2, (mem_inter.1 hy).2⟩
  exact hne (h1.trans h2.symm)

/-- An STS on a `v`-set has exactly `v(v-1)/6` blocks: `3 |B| = C(v, 2)`. -/
lemma three_mul_card_blocks {B : Finset (Finset Y)} (hB : IsSTS B) :
    3 * B.card = (Fintype.card Y).choose 2 := by
  have hU : B.biUnion (fun A => A.powersetCard 2) = (univ : Finset Y).powersetCard 2 := by
    ext P
    simp only [mem_biUnion, mem_powersetCard, subset_univ, true_and]
    constructor
    · rintro ⟨A, -, -, hP⟩; exact hP
    · intro hP
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hP
      obtain ⟨A, ⟨hA, hx, hy⟩, -⟩ := hB.2 x y hxy
      refine ⟨A, hA, ?_, hP⟩
      intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
  have hcard := congrArg Finset.card hU
  rw [card_powersetCard, card_univ, card_biUnion] at hcard
  · rw [← hcard, sum_const_nat (m := 3)]
    · ring
    · intro A hA; rw [card_powersetCard, hB.1 A hA]; rfl
  · intro A hA A' hA' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro P hP hP'
    rw [mem_powersetCard] at hP hP'
    have := inter_card_le_one hB hA hA' hne
    have : P ⊆ A ∩ A' := subset_inter hP.1 hP'.1
    have := card_le_card this
    omega

end blocks

/-! ### Sequences of blocks pairwise meeting in at most one point -/

/-- Sequences `(A₁, …, A_t)` of 3-subsets of `Fin v` such that no 2-subset is contained in
two of them. -/
def Good (v t : ℕ) : Type :=
  {s : Fin t → Finset (Fin v) // (∀ i, (s i).card = 3) ∧ ∀ i j, i ≠ j → (s i ∩ s j).card ≤ 1}

noncomputable instance (v t : ℕ) : Fintype (Good v t) := by
  unfold Good; infer_instance

/-- The candidates for the next element of a good sequence. -/
def cand {v t : ℕ} (s : Fin t → Finset (Fin v)) : Finset (Finset (Fin v)) :=
  ((univ : Finset (Fin v)).powersetCard 3).filter (fun A => ∀ i, (A ∩ s i).card ≤ 1)

lemma cand_sq_le {v t : ℕ} (s : Good v t) :
    ((cand s.1).card : ℝ) ^ 2 ≤ 2 / 9 * ((v.choose 2 - 3 * t : ℕ) : ℝ) ^ 3 := by
  set U := (univ : Finset (Fin t)).biUnion (fun i => (s.1 i).powersetCard 2)
  set E := ((univ : Finset (Fin v)).powersetCard 2) \ U
  have hUcard : U.card = 3 * t := by
    rw [card_biUnion]
    · rw [sum_const_nat (m := 3)]
      · simp [mul_comm]
      · intro i _; rw [card_powersetCard, s.2.1 i]; rfl
    · intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro P hP hP'
      rw [mem_powersetCard] at hP hP'
      have := s.2.2 i j hij
      have := card_le_card (subset_inter hP.1 hP'.1)
      omega
  have hUsub : U ⊆ (univ : Finset (Fin v)).powersetCard 2 := by
    intro P hP
    simp only [U, mem_biUnion, mem_powersetCard] at hP
    obtain ⟨i, -, -, hP⟩ := hP
    simpa using hP
  have hEcard : E.card = v.choose 2 - 3 * t := by
    rw [card_sdiff_of_subset hUsub, hUcard, card_powersetCard, card_univ, Fintype.card_fin]
  have hE2 : ∀ e ∈ E, e.card = 2 := by
    intro e he; simp only [E, mem_sdiff, mem_powersetCard] at he; exact he.1.2
  have hsub : cand s.1 ⊆ triangles E := by
    intro A hA
    simp only [cand, mem_filter, mem_powersetCard] at hA
    simp only [triangles, mem_filter, mem_powersetCard, subset_univ, true_and]
    refine ⟨hA.1.2, ?_⟩
    intro P hP
    rw [mem_powersetCard] at hP
    simp only [E, mem_sdiff, mem_powersetCard, subset_univ, true_and]
    refine ⟨hP.2, ?_⟩
    intro hPU
    simp only [U, mem_biUnion, mem_univ, true_and, mem_powersetCard] at hPU
    obtain ⟨i, hi, -⟩ := hPU
    have := card_le_card (subset_inter hP.1 hi)
    have := hA.2 i
    omega
  have h1 : ((cand s.1).card : ℝ) ≤ Real.sqrt 2 / 3 * (E.card : ℝ) ^ (3 / 2 : ℝ) :=
    le_trans (by exact_mod_cast card_le_card hsub) (triangles_le_sqrt E hE2)
  rw [← hEcard]
  have h0 : (0 : ℝ) ≤ ((cand s.1).card : ℝ) := by positivity
  calc ((cand s.1).card : ℝ) ^ 2 ≤ (Real.sqrt 2 / 3 * (E.card : ℝ) ^ (3 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ = 2 / 9 * (E.card : ℝ) ^ 3 := by
        have : ((E.card : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (E.card : ℝ) ^ 3 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num), this]; norm_num

/-- Extending good sequences by one element. -/
lemma card_good_succ_le (v t : ℕ) :
    Fintype.card (Good v (t + 1)) ≤ ∑ s : Good v t, (cand s.1).card := by
  classical
  let f : Good v (t + 1) → Σ s : Good v t, cand s.1 := fun s =>
    ⟨⟨Fin.init s.1, fun i => s.2.1 _, fun i j hij => s.2.2 _ _ (by
      intro h; exact hij (Fin.castSucc_injective _ h))⟩,
     ⟨s.1 (Fin.last t), by
        simp only [cand, mem_filter, mem_powersetCard, subset_univ, true_and]
        refine ⟨s.2.1 _, fun i => s.2.2 _ _ ?_⟩
        exact (Fin.castSucc_lt_last i).ne'⟩⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have h1' : Fin.init a.1 = Fin.init b.1 :=
      congrArg (fun x : (Σ s : Good v t, cand s.1) => x.1.1) h
    have h2' : a.1 (Fin.last t) = b.1 (Fin.last t) :=
      congrArg (fun x : (Σ s : Good v t, cand s.1) => (x.2 : Finset (Fin v))) h
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact h2'
    · exact congrFun h1' j
  have := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at this
  simpa using this

/-- The number of good sequences of length `t ≤ b`, when `C(v,2) = 3b`. -/
lemma card_good_sq (v b : ℕ) (hb : v.choose 2 = 3 * b) :
    ∀ t, t ≤ b → ((Fintype.card (Good v t) : ℝ)) ^ 2 * (((b - t).factorial : ℝ)) ^ 3 ≤
      6 ^ t * ((b.factorial : ℝ)) ^ 3 := by
  intro t
  induction t with
  | zero =>
    intro _
    have : Fintype.card (Good v 0) = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩, fun s => ?_⟩
      apply Subtype.ext; funext i; exact i.elim0
    simp [this]
  | succ t ih =>
    intro ht
    have ih := ih (by omega)
    have hq : ((v.choose 2 - 3 * t : ℕ) : ℝ) = 3 * ((b - t : ℕ) : ℝ) := by
      rw [hb]; push_cast [show 3 * b - 3 * t = 3 * (b - t) by omega]; push_cast; ring
    -- bound on the next count
    have hstep : ((Fintype.card (Good v (t + 1)) : ℝ)) ≤
        (Fintype.card (Good v t) : ℝ) * Real.sqrt (6 * ((b - t : ℕ) : ℝ) ^ 3) := by
      have h1 : ((Fintype.card (Good v (t + 1)) : ℝ)) ≤ ∑ s : Good v t, ((cand s.1).card : ℝ) := by
        exact_mod_cast card_good_succ_le v t
      refine h1.trans ?_
      have : ∀ s : Good v t, ((cand s.1).card : ℝ) ≤ Real.sqrt (6 * ((b - t : ℕ) : ℝ) ^ 3) := by
        intro s
        apply Real.le_sqrt_of_sq_le
        have := cand_sq_le s
        rw [hq] at this
        nlinarith
      calc ∑ s : Good v t, ((cand s.1).card : ℝ) ≤ ∑ _s : Good v t,
            Real.sqrt (6 * ((b - t : ℕ) : ℝ) ^ 3) := Finset.sum_le_sum (fun s _ => this s)
        _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
    have hsq : ((Fintype.card (Good v (t + 1)) : ℝ)) ^ 2 ≤
        (Fintype.card (Good v t) : ℝ) ^ 2 * (6 * ((b - t : ℕ) : ℝ) ^ 3) := by
      have h0 : (0:ℝ) ≤ (Fintype.card (Good v (t + 1)) : ℝ) := by positivity
      calc ((Fintype.card (Good v (t + 1)) : ℝ)) ^ 2 ≤
          ((Fintype.card (Good v t) : ℝ) * Real.sqrt (6 * ((b - t : ℕ) : ℝ) ^ 3)) ^ 2 :=
            pow_le_pow_left₀ h0 hstep 2
        _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hfac : ((b - t).factorial : ℝ) = ((b - t : ℕ) : ℝ) * ((b - (t + 1)).factorial : ℝ) := by
      rw [show b - t = (b - (t + 1)) + 1 by omega, Nat.factorial_succ]; push_cast; ring
    have hpos : (0 : ℝ) ≤ (((b - (t + 1)).factorial : ℝ)) ^ 3 := by positivity
    calc ((Fintype.card (Good v (t + 1)) : ℝ)) ^ 2 * (((b - (t + 1)).factorial : ℝ)) ^ 3
        ≤ (Fintype.card (Good v t) : ℝ) ^ 2 * (6 * ((b - t : ℕ) : ℝ) ^ 3) *
            (((b - (t + 1)).factorial : ℝ)) ^ 3 := mul_le_mul_of_nonneg_right hsq hpos
      _ = 6 * ((Fintype.card (Good v t) : ℝ) ^ 2 * (((b - t).factorial : ℝ)) ^ 3) := by
          rw [hfac]; ring
      _ ≤ 6 * (6 ^ t * ((b.factorial : ℝ)) ^ 3) := by linarith
      _ = 6 ^ (t + 1) * ((b.factorial : ℝ)) ^ 3 := by ring

/-- Every STS of order `v` with `b` blocks gives `b!` good sequences of length `b`. -/
lemma factorial_mul_D_le (v b : ℕ) (hb : ∀ B : STSOn v, B.1.card = b) :
    b.factorial * D v ≤ Fintype.card (Good v b) := by
  classical
  let f : (Σ B : STSOn v, (Fin b ≃ B.1)) → Good v b := fun p =>
    ⟨fun i => (p.2 i).1, fun i => p.1.2.1 _ (p.2 i).2, fun i j hij =>
      inter_card_le_one p.1.2 (p.2 i).2 (p.2 j).2 (by
        intro h; exact hij (p.2.injective (Subtype.ext h)))⟩
  have hf : Function.Injective f := by
    rintro ⟨B₁, f₁⟩ ⟨B₂, f₂⟩ h
    have hfun : ∀ i, (f₁ i).1 = (f₂ i).1 := fun i => congrFun (congrArg Subtype.val h) i
    have hB : B₁ = B₂ := by
      apply Subtype.ext
      ext A
      constructor
      · intro hA
        obtain ⟨i, hi⟩ := f₁.surjective ⟨A, hA⟩
        have : A = (f₂ i).1 := by rw [← hfun i, hi]
        rw [this]; exact (f₂ i).2
      · intro hA
        obtain ⟨i, hi⟩ := f₂.surjective ⟨A, hA⟩
        have : A = (f₁ i).1 := by rw [hfun i, hi]
        rw [this]; exact (f₁ i).2
    subst hB
    have : f₁ = f₂ := Equiv.ext (fun i => Subtype.ext (hfun i))
    subst this
    rfl
  have := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at this
  have hc : ∀ B : STSOn v, Fintype.card (Fin b ≃ B.1) = b.factorial := by
    intro B
    have hcardB : Fintype.card (B.1 : Finset (Finset (Fin v))) = b := by simp [hb B]
    rw [Fintype.card_equiv ((Fintype.equivFinOfCardEq hcardB).symm), Fintype.card_fin]
  simp only [hc, sum_const, card_univ, smul_eq_mul] at this
  rw [D, Nat.card_eq_fintype_card]
  linarith

/-- A consequence of Stirling's formula: `n! ≤ e √n (n/e)^n` for `n ≥ 1`. -/
lemma factorial_le_stirling (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  simp only [Function.comp_apply, zero_add, Stirling.stirlingSeq_one] at h
  unfold Stirling.stirlingSeq at h
  push_cast at h ⊢
  have hpos : 0 < Real.sqrt (2 * ((m : ℝ) + 1)) * (((m : ℝ) + 1) / Real.exp 1) ^ (m + 1) := by
    positivity
  rw [div_le_iff₀ hpos] at h
  refine h.trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by norm_num)]
  have : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- **Theorem 1.** For every `v ≥ 7`, `N(v) < (e^{-1/2} v)^{v²/6}`. -/
theorem theorem1 (v : ℕ) (hv : 7 ≤ v) :
    (N v : ℝ) < (Real.exp (-1 / 2) * v) ^ ((v : ℝ) ^ 2 / 6) := by
  have hv' : (7 : ℝ) ≤ v := by exact_mod_cast hv
  have hbase : 0 < Real.exp (-1 / 2) * v := by positivity
  have hR : 0 < (Real.exp (-1 / 2) * v) ^ ((v : ℝ) ^ 2 / 6) := Real.rpow_pos_of_pos hbase _
  by_cases hD : D v = 0
  · have : N v = 0 := by have := N_le_D v; omega
    rw [this]; simpa using hR
  have hne : Nonempty (STSOn v) := by
    rw [D] at hD
    exact (Nat.card_ne_zero.1 hD).1
  obtain ⟨B⟩ := hne
  set b := B.1.card with hbdef
  have h3 : ∀ B' : STSOn v, 3 * B'.1.card = v.choose 2 := by
    intro B'; have := three_mul_card_blocks B'.2; simpa using this
  have hb3 : v.choose 2 = 3 * b := (h3 B).symm
  have hball : ∀ B' : STSOn v, B'.1.card = b := by
    intro B'; have := h3 B'; omega
  have h1 := factorial_mul_D_le v b hball
  have h2 := card_good_sq v b hb3 b le_rfl
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one] at h2
  -- 6 b = v (v - 1)
  have hb6 : (6 * b : ℝ) = v * (v - 1) := by
    have : 2 * v.choose 2 = v * (v - 1) := by rw [Nat.choose_two_right]; exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self v)
    have h' : (2 * v.choose 2 : ℕ) = 6 * b := by omega
    have : ((v * (v - 1) : ℕ) : ℝ) = 6 * b := by rw [← this, h']; push_cast; ring
    rw [← this]; push_cast [show 1 ≤ v by omega]; ring
  have hb1 : 1 ≤ b := by
    have : (6 : ℝ) ≤ 6 * b := by rw [hb6]; nlinarith
    have : (1 : ℝ) ≤ b := by linarith
    exact_mod_cast this
  -- D² ≤ 6^b b!
  have hfpos : (0 : ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
  have hD2 : (D v : ℝ) ^ 2 ≤ 6 ^ b * b.factorial := by
    have h1' : (b.factorial : ℝ) * D v ≤ Fintype.card (Good v b) := by exact_mod_cast h1
    have h0 : (0:ℝ) ≤ (b.factorial : ℝ) * D v := by positivity
    have : ((b.factorial : ℝ) * D v) ^ 2 ≤ 6 ^ b * (b.factorial : ℝ) ^ 3 :=
      (pow_le_pow_left₀ h0 h1' 2).trans h2
    have : (b.factorial : ℝ) ^ 2 * ((D v : ℝ) ^ 2) ≤ (b.factorial : ℝ) ^ 2 * (6 ^ b * b.factorial) := by
      nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hst := factorial_le_stirling b hb1
  set x : ℝ := (v : ℝ) ^ 2 / Real.exp 1 with hx
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he3 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hx1 : 1 ≤ x := by
    rw [hx, le_div_iff₀ he]; nlinarith
  -- 6^b b! ≤ e √b x^b
  have hA : (6 : ℝ) ^ b * b.factorial ≤ Real.exp 1 * Real.sqrt b * x ^ b := by
    calc (6 : ℝ) ^ b * b.factorial ≤ 6 ^ b * (Real.exp 1 * Real.sqrt b * (b / Real.exp 1) ^ b) :=
          mul_le_mul_of_nonneg_left hst (by positivity)
      _ = Real.exp 1 * Real.sqrt b * (6 * b / Real.exp 1) ^ b := by
          rw [show (6 * b / Real.exp 1 : ℝ) = 6 * (b / Real.exp 1) by ring, mul_pow]; ring
      _ ≤ Real.exp 1 * Real.sqrt b * x ^ b := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          rw [hx, hb6]
          apply div_le_div_of_nonneg_right _ he.le
          nlinarith
  -- e √b < x ≤ x^{v/6}
  have hB : Real.exp 1 * Real.sqrt b < x := by
    have hsq : (Real.exp 1 * Real.sqrt b) ^ 2 < x ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hx, div_pow]
      rw [lt_div_iff₀ (by positivity)]
      have hb' : (b : ℝ) ≤ (v : ℝ) ^ 2 / 6 := by nlinarith
      have he4 : Real.exp 1 ^ 4 < 55 := by
        have : Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := pow_lt_pow_left₀ he3 he.le (by norm_num)
        linarith [show (2.7182818286 : ℝ) ^ 4 < 55 by norm_num]
      have : Real.exp 1 ^ 2 * b * Real.exp 1 ^ 2 = Real.exp 1 ^ 4 * b := by ring
      rw [this]
      have hb0 : (0:ℝ) ≤ b := by positivity
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  have hC : x ≤ x ^ ((v : ℝ) / 6) := by
    conv_lhs => rw [← Real.rpow_one x]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hxpow : x ^ ((v : ℝ) ^ 2 / 6) = x ^ b * x ^ ((v : ℝ) / 6) := by
    rw [← Real.rpow_natCast x b, ← Real.rpow_add (by positivity)]
    congr 1
    linarith
  have hD2' : (D v : ℝ) ^ 2 < x ^ ((v : ℝ) ^ 2 / 6) := by
    rw [hxpow]
    calc (D v : ℝ) ^ 2 ≤ Real.exp 1 * Real.sqrt b * x ^ b := hD2.trans hA
      _ = x ^ b * (Real.exp 1 * Real.sqrt b) := by ring
      _ < x ^ b * x ^ ((v : ℝ) / 6) := by
          apply mul_lt_mul_of_pos_left (hB.trans_le hC) (by positivity)
  have hRsq : ((Real.exp (-1 / 2) * v) ^ ((v : ℝ) ^ 2 / 6)) ^ 2 = x ^ ((v : ℝ) ^ 2 / 6) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le, mul_comm ((v : ℝ) ^ 2 / 6),
      Real.rpow_mul hbase.le]
    congr 1
    rw [Real.rpow_natCast, mul_pow, hx, ← Real.exp_nat_mul,
      show ((2 : ℕ) : ℝ) * (-1 / 2) = -1 by norm_num, Real.exp_neg]
    field_simp
  have hN : (N v : ℝ) ≤ D v := by exact_mod_cast N_le_D v
  have hN2 : (N v : ℝ) ^ 2 < ((Real.exp (-1 / 2) * v) ^ ((v : ℝ) ^ 2 / 6)) ^ 2 := by
    rw [hRsq]
    exact lt_of_le_of_lt (pow_le_pow_left₀ (by positivity) hN 2) hD2'
  exact lt_of_pow_lt_pow_left₀ 2 hR.le hN2

end STS
