/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.T4Perm
public import RequestProject.Lemma5
public import RequestProject.SmallSTS

/-!
# Theorem 4: lower bounds for `N(19)`, `N(21)`, `N(25)`
-/

@[expose] public section

open Finset

namespace STS

open T4

attribute [local irreducible] Ccon

/-! ### Theorem 4 (ii) -/

/-- The 7-flats of the constructed systems of order 21 are exactly `Z₀, Z₁, Z₂`. -/
lemma flat7_eq_R {c : Finset (Finset (Pt 0 7))} (hc : c ∈ Ccon 0 7) {Y : Finset (Pt 0 7)}
    (hY : IsFlat c Y) (h7 : Y.card = 7) : ∃ j, Y = Rset 0 7 j := by
  rcases flat_dichotomy (show 0 ≤ 1 by norm_num) hc hY with ⟨j, hj⟩ | ⟨h1, h2⟩
  · refine ⟨j, eq_of_subset_of_card_le hj ?_⟩
    rw [card_Rset, h7]
  · have hs := card_eq_split Y
    have hW : (Y ∩ Wset 0 7).card ≤ 0 := by
      have := card_le_card (inter_subset_right (s₁ := Y) (s₂ := Wset 0 7))
      rwa [card_Wset] at this
    omega

theorem theorem4_ii_aux : (Ccon 0 7).card ≤ (6 * Nat.factorial 7 ^ 3) * N 21 := by
  have e : Pt 0 7 ≃ Fin 21 := Fintype.equivFinOfCardEq (by rw [card_Pt])
  refine card_le_mul_N e _ (fun c hc => isSTS_of_mem_Ccon (by norm_num) hc) _ ?_
  intro c0 hc0
  refine le_trans (card_le_card ?_) (card_perm_R (by norm_num) (by norm_num))
  intro σ hσ
  simp only [mem_filter, mem_univ, true_and] at hσ ⊢
  intro i
  apply flat7_eq_R hσ
  · exact IsFlat.mapBlocks_equiv σ (flat_Rset (by norm_num) hc0 i)
  · rw [card_image_of_injective _ σ.injective, card_Rset]

/-- **Theorem 4 (ii).** `N(21) ≥ 2160980`. -/
theorem theorem4_ii : 2160980 ≤ N 21 := by
  have h1 := theorem4_ii_aux
  rw [card_Ccon (by norm_num), card_Sys, lemma5_ii] at h1
  have h2 := D7_ge
  have h3 : Nat.factorial 7 * Nat.factorial 6 * 16942080 * 30 ^ 3 ≤
      Nat.factorial 7 * Nat.factorial 6 * 16942080 * D (0 + 7) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 3)
  by_contra h
  push_neg at h
  have h4 := Nat.mul_le_mul_left (6 * Nat.factorial 7 ^ 3) (Nat.le_of_lt_succ h)
  simp only [Nat.factorial, Nat.succ_eq_add_one] at h1 h3 h4
  norm_num at h1 h3 h4
  omega

/-! ### Theorem 4 (iii) -/

lemma card_inter_Rset (Y : Finset (Pt w m)) (j : Fin 3) :
    (Y ∩ Rset w m j).card = (Y ∩ Wset w m).card + (Y ∩ Zset w m j).card := by
  rw [Rset_eq, inter_union_distrib_left, card_union_of_disjoint]
  exact Disjoint.mono inter_subset_right inter_subset_right (disjoint_WZ j)

/-- The 9-flats of the constructed systems of order 25. -/
lemma flat9 {c : Finset (Finset (Pt 1 8))} (hc : c ∈ Ccon 1 8) {Y : Finset (Pt 1 8)}
    (hY : IsFlat c Y) (h9 : Y.card = 9) :
    (∃ j, Y = Rset 1 8 j) ∨ (Sum.inl 0 ∉ Y ∧ ∀ j, (Y ∩ Rset 1 8 j).card = 3) := by
  rcases flat_dichotomy (show 1 ≤ 1 by norm_num) hc hY with ⟨j, hj⟩ | ⟨h1, h2⟩
  · left
    refine ⟨j, eq_of_subset_of_card_le hj ?_⟩
    rw [card_Rset, h9]
  · right
    have hs := card_eq_split Y
    have hW : (Y ∩ Wset 1 8).card ≤ 1 := by
      have := card_le_card (inter_subset_right (s₁ := Y) (s₂ := Wset 1 8))
      rwa [card_Wset] at this
    have hW0 : (Y ∩ Wset 1 8).card = 0 := by omega
    refine ⟨fun h => ?_, fun j => ?_⟩
    · have : Sum.inl 0 ∈ Y ∩ Wset 1 8 := mem_inter.2 ⟨h, by simp [mem_Wset]⟩
      rw [card_eq_zero.1 hW0] at this
      simp at this
    · rw [card_inter_Rset, hW0]
      fin_cases j <;> simp <;> omega

lemma card_image_Rset_inter (σ : Equiv.Perm (Pt w m)) {i k : Fin 3} (hik : i ≠ k) :
    ((Rset w m i).image σ ∩ (Rset w m k).image σ).card = w := by
  rw [← image_inter_of_injOn _ _ σ.injective.injOn, card_image_of_injective _ σ.injective,
    Rset_inter hik, card_Wset]

theorem theorem4_iii_aux : (Ccon 1 8).card ≤ (6 * Nat.factorial 8 ^ 3) * N 25 := by
  have e : Pt 1 8 ≃ Fin 25 := Fintype.equivFinOfCardEq (by rw [card_Pt])
  refine card_le_mul_N e _ (fun c hc => isSTS_of_mem_Ccon (by norm_num) hc) _ ?_
  intro c0 hc0
  refine le_trans (card_le_card ?_) (card_perm_R (by norm_num) (by norm_num))
  intro σ hσ
  simp only [mem_filter, mem_univ, true_and] at hσ ⊢
  have hfl : ∀ i, (∃ j, (Rset 1 8 i).image σ = Rset 1 8 j) ∨
      (Sum.inl 0 ∉ (Rset 1 8 i).image σ ∧ ∀ j, ((Rset 1 8 i).image σ ∩ Rset 1 8 j).card = 3) :=
    fun i => flat9 hσ (IsFlat.mapBlocks_equiv σ (flat_Rset (by norm_num) hc0 i))
      (by rw [card_image_of_injective _ σ.injective, card_Rset])
  obtain ⟨i0, hi0⟩ : ∃ i, Sum.inl 0 ∈ (Rset 1 8 i).image σ := by
    obtain ⟨x, hx⟩ := σ.surjective (Sum.inl 0)
    obtain ⟨i, hi⟩ : ∃ i, x ∈ Rset 1 8 i := by
      rcases cover x with h | h | h | h
      · exact ⟨0, by rw [Rset_eq]; exact mem_union_left _ h⟩
      · exact ⟨0, by rw [Rset_eq]; exact mem_union_right _ h⟩
      · exact ⟨1, by rw [Rset_eq]; exact mem_union_right _ h⟩
      · exact ⟨2, by rw [Rset_eq]; exact mem_union_right _ h⟩
    exact ⟨i, hx ▸ mem_image_of_mem _ hi⟩
  obtain ⟨j0, hj0⟩ : ∃ j, (Rset 1 8 i0).image σ = Rset 1 8 j := by
    rcases hfl i0 with h | h
    · exact h
    · exact absurd hi0 h.1
  intro k
  by_cases hk : k = i0
  · subst hk; exact ⟨j0, hj0⟩
  rcases hfl k with h | h
  · exact h
  · have h1 := h.2 j0
    rw [← hj0, card_image_Rset_inter σ hk] at h1
    omega

/-- **Theorem 4 (iii).** `N(25) ≥ 163929929318400`. -/
theorem theorem4_iii : 163929929318400 ≤ N 25 := by
  have h1 := theorem4_iii_aux
  rw [card_Ccon (by norm_num), card_Sys, lemma5_iii] at h1
  have h2 := D9_ge
  have h3 : 108776032459082956800 * 840 ^ 3 ≤ 108776032459082956800 * D (1 + 8) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 3)
  by_contra h
  push_neg at h
  have h4 := Nat.mul_le_mul_left (6 * Nat.factorial 8 ^ 3) (Nat.le_of_lt_succ h)
  simp only [Nat.factorial, Nat.succ_eq_add_one] at h1 h3 h4
  norm_num at h1 h3 h4
  omega

end STS
