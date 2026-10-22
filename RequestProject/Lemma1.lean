/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.UpperBound

/-!
# Lemma 1 of the paper

If a simple graph has `q = C(k,2) + j` edges with `0 ≤ j < k`, then it has at most
`C(k,3) + C(j,2)` triangles.
-/

@[expose] public section

open Finset

namespace STS

lemma choose_two_q (m : ℕ) : ((m.choose 2 : ℕ) : ℚ) = m * (m - 1) / 2 := Nat.cast_choose_two ℚ m

/-- The numerical step in the proof of Lemma 1. -/
lemma kk_step (k j d : ℕ) (hj : j < k) (hd1 : 1 ≤ d) (hdk : d + 1 ≤ k) :
    ∃ k' j', j' < k' ∧ k.choose 2 + j - d = k'.choose 2 + j' ∧
      k'.choose 3 + j'.choose 2 + d.choose 2 ≤ k.choose 3 + j.choose 2 := by
  rcases le_or_gt d j with hdj | hdj
  · refine ⟨k, j - d, by omega, by omega, ?_⟩
    have : (j - d).choose 2 + d.choose 2 ≤ j.choose 2 := by
      have h : (((j - d).choose 2 + d.choose 2 : ℕ) : ℚ) ≤ ((j.choose 2 : ℕ) : ℚ) := by
        push_cast [choose_two_q, Nat.cast_sub hdj]
        have h1 : (0 : ℚ) ≤ (j : ℚ) - d := by
          have : (d : ℚ) ≤ j := by exact_mod_cast hdj
          linarith
        have h2 : (0 : ℚ) ≤ d := by positivity
        nlinarith [mul_nonneg h1 h2]
      exact_mod_cast h
    omega
  · obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    have hK : (K + 1).choose 3 = K.choose 2 + K.choose 3 := Nat.choose_succ_succ' K 2
    have hK2 : (K + 1).choose 2 = K.choose 1 + K.choose 2 := Nat.choose_succ_succ' K 1
    rw [Nat.choose_one_right] at hK2
    refine ⟨K, K + j - d, by omega, by omega, ?_⟩
    have key : (K + j - d).choose 2 + d.choose 2 ≤ K.choose 2 + j.choose 2 := by
      have h : (((K + j - d).choose 2 + d.choose 2 : ℕ) : ℚ) ≤
          ((K.choose 2 + j.choose 2 : ℕ) : ℚ) := by
        push_cast [choose_two_q, Nat.cast_sub (show d ≤ K + j by omega)]
        have h1 : (0 : ℚ) ≤ (d : ℚ) - j := by
          have : (j : ℚ) ≤ d := by exact_mod_cast hdj.le
          linarith
        have h2 : (0 : ℚ) ≤ (K : ℚ) - d := by
          have : (d : ℚ) ≤ K := by exact_mod_cast (show d ≤ K by omega)
          linarith
        nlinarith [mul_nonneg h1 h2]
      exact_mod_cast h
    omega

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Removing the edges through `x`. -/
lemma triangles_le_remove (E : Finset (Finset X)) (hE : ∀ e ∈ E, e.card = 2) (x : X) :
    (triangles E).card ≤ ((E.filter (x ∈ ·)).card).choose 2 +
      (triangles (E.filter (x ∉ ·))).card := by
  have hsplit : triangles E = (triangles E).filter (x ∈ ·) ∪ (triangles E).filter (x ∉ ·) := by
    ext A; simp only [mem_union, mem_filter]; tauto
  calc (triangles E).card ≤ ((triangles E).filter (x ∈ ·)).card +
        ((triangles E).filter (x ∉ ·)).card := by
        conv_lhs => rw [hsplit]
        exact card_union_le _ _
    _ ≤ _ := by
        apply add_le_add (tri_w_le_choose E hE x)
        apply card_le_card
        intro A hA
        simp only [mem_filter, triangles, mem_powersetCard, subset_univ, true_and] at hA ⊢
        refine ⟨hA.1.1, ?_⟩
        intro P hP
        rw [mem_filter]
        refine ⟨hA.1.2 hP, ?_⟩
        intro hxP
        exact hA.2 ((mem_powersetCard.1 hP).1 hxP)

/-- In a nonempty graph with fewer than `C(k+1, 2)` edges some vertex has degree between
`1` and `k - 1`. -/
lemma exists_small_degree (E : Finset (Finset X)) (hE : ∀ e ∈ E, e.card = 2) (k : ℕ)
    (hne : E.Nonempty) (hlt : E.card < (k + 1).choose 2) :
    ∃ x, 1 ≤ (E.filter (x ∈ ·)).card ∧ (E.filter (x ∈ ·)).card + 1 ≤ k := by
  by_contra hcon
  push_neg at hcon
  -- every non-isolated vertex has degree ≥ k
  have hbig : ∀ x, 1 ≤ (E.filter (x ∈ ·)).card → k ≤ (E.filter (x ∈ ·)).card := by
    intro x hx; have := hcon x hx; omega
  obtain ⟨e, he⟩ := hne
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 (hE e he)
  have hx1 : 1 ≤ (E.filter (x ∈ ·)).card :=
    Finset.card_pos.2 ⟨_, mem_filter.2 ⟨he, by simp⟩⟩
  -- the neighbourhood of x
  set T := univ.filter (fun z => z ≠ x ∧ ({x, z} : Finset X) ∈ E)
  have hT : (E.filter (x ∈ ·)).card ≤ T.card := by
    refine card_le_card_of_surjOn (fun z => ({x, z} : Finset X)) ?_
    intro P hP
    simp only [coe_filter, Set.mem_setOf_eq] at hP
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (hE _ hP.1)
    simp only [mem_insert, mem_singleton] at hP
    rcases hP.2 with rfl | rfl
    · refine ⟨b, ?_, rfl⟩
      simp only [T, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      exact ⟨hab.symm, hP.1⟩
    · refine ⟨a, ?_, ?_⟩
      · simp only [T, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
        exact ⟨hab, by rw [Finset.pair_comm]; exact hP.1⟩
      · exact Finset.pair_comm _ _
  set S := univ.filter (fun z => 1 ≤ (E.filter (z ∈ ·)).card)
  have hTS : insert x T ⊆ S := by
    intro z hz
    simp only [S, mem_filter, mem_univ, true_and]
    rw [mem_insert] at hz
    rcases hz with rfl | hz
    · exact hx1
    · simp only [T, mem_filter, mem_univ, true_and] at hz
      exact Finset.card_pos.2 ⟨_, mem_filter.2 ⟨hz.2, by simp⟩⟩
  have hxT : x ∉ T := by simp [T]
  have hS : k + 1 ≤ S.card := by
    have := card_le_card hTS
    rw [card_insert_of_notMem hxT] at this
    have := hbig x hx1
    omega
  have hsum : k * S.card ≤ 2 * E.card := by
    rw [mul_comm 2 E.card, ← sum_const_nat (m := 2) hE, ← sum_card_filter_mem]
    calc k * S.card = ∑ _z ∈ S, k := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ z ∈ S, (E.filter (z ∈ ·)).card := by
          apply sum_le_sum; intro z hz
          simp only [S, mem_filter, mem_univ, true_and] at hz
          exact hbig z hz
      _ ≤ ∑ z, (E.filter (z ∈ ·)).card := sum_le_sum_of_subset (subset_univ _)
  have h2 : 2 * (k + 1).choose 2 = (k + 1) * k := by
    rw [Nat.choose_two_right]
    have := Nat.even_mul_pred_self (k + 1)
    simpa using Nat.two_mul_div_two_of_even this
  nlinarith

/-- **Lemma 1.** Let `(X, E)` be a simple graph (`E` a set of 2-subsets of `X`) with
`|E| = q = C(k,2) + j`, `0 ≤ j < k`. Then the number of triangles of `(X, E)` is at most
`C(k,3) + C(j,2)`. -/
theorem lemma1 (E : Finset (Finset X)) (hE : ∀ e ∈ E, e.card = 2) (k j : ℕ) (hj : j < k)
    (hq : E.card = k.choose 2 + j) : (triangles E).card ≤ k.choose 3 + j.choose 2 := by
  induction hn : E.card using Nat.strong_induction_on generalizing E k j with
  | _ n ih =>
    rcases E.eq_empty_or_nonempty with h0 | hne
    · subst h0
      have : (triangles (∅ : Finset (Finset X))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro A hA
        simp only [triangles, mem_filter, mem_powersetCard, subset_empty] at hA
        have : A.powersetCard 2 = ∅ := hA.2
        rw [Finset.powersetCard_eq_empty, hA.1.2] at this
        omega
      omega
    · have hlt : E.card < (k + 1).choose 2 := by
        have : (k + 1).choose 2 = k.choose 1 + k.choose 2 := Nat.choose_succ_succ' k 1
        rw [Nat.choose_one_right] at this
        omega
      obtain ⟨x, hd1, hdk⟩ := exists_small_degree E hE k hne hlt
      have h2 := triangles_le_remove E hE x
      set d := (E.filter (x ∈ ·)).card with hd
      obtain ⟨k', j', hj', hq', hineq⟩ := kk_step k j d hj hd1 hdk
      have hE' : ∀ e ∈ E.filter (x ∉ ·), e.card = 2 := fun e he => hE e (mem_filter.1 he).1
      have hcard' : (E.filter (x ∉ ·)).card = E.card - d := by
        have := Finset.card_filter_add_card_filter_not (s := E) (fun e => x ∈ e)
        omega
      have hpos : 0 < E.card := hne.card_pos
      have hlt' : (E.filter (x ∉ ·)).card < n := by omega
      have := ih _ hlt' (E.filter (x ∉ ·)) hE' k' j' hj' (by omega) rfl
      omega

end STS
