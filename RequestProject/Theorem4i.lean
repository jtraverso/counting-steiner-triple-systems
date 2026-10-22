/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Theorem4

/-!
# Theorem 4 (i): `N(19) ≥ 2450`

The constructed systems of order 19 live on `Pt 1 6 = Fin 1 ⊕ (Fin 3 × Fin 6)`, the special
point being `0 = Sum.inl 0`. Every 7-flat contains `0`; a permutation mapping one constructed
system onto another maps some triad of the first system onto `{R₀, R₁, R₂}`, and a system has
at most 4 triads (here: at most 4 "distinguished" 7-flats through a fixed block `A ∋ 0`).
-/

@[expose] public section

open Finset

namespace STS

open T4

attribute [local irreducible] Ccon

lemma Wset_one_six : Wset 1 6 = {Sum.inl 0} := by
  ext x
  cases x with
  | inl a => simp [Wset, Subsingleton.elim a 0]
  | inr p => simp [Wset]

/-- Every 7-flat of a constructed system of order 19 contains the special point `0`. -/
lemma flat7_zero {c : Finset (Finset (Pt 1 6))} (hc : c ∈ Ccon 1 6) {Y : Finset (Pt 1 6)}
    (hY : IsFlat c Y) (h7 : Y.card = 7) : Sum.inl 0 ∈ Y := by
  by_contra h
  rcases flat_dichotomy (show 1 ≤ 1 by norm_num) hc hY with ⟨j, hj⟩ | ⟨h1, h2⟩
  · have hYe : Y = Rset 1 6 j := eq_of_subset_of_card_le hj (by rw [card_Rset, h7])
    apply h
    rw [hYe, Rset_eq, Wset_one_six]
    exact mem_union_left _ (mem_singleton_self _)
  · have hs := card_eq_split Y
    have hW : (Y ∩ Wset 1 6).card = 0 := by
      rw [Wset_one_six, inter_singleton_of_notMem h, card_empty]
    omega

/-- A 7-flat different from `R₀, R₁, R₂` meets each `Rₖ` in exactly 3 points. -/
lemma flat7_meet3 {c : Finset (Finset (Pt 1 6))} (hc : c ∈ Ccon 1 6) {Y : Finset (Pt 1 6)}
    (hY : IsFlat c Y) (h7 : Y.card = 7) (hne : ∀ j, Y ≠ Rset 1 6 j) (k : Fin 3) :
    (Y ∩ Rset 1 6 k).card = 3 := by
  rcases flat_dichotomy (show 1 ≤ 1 by norm_num) hc hY with ⟨j, hj⟩ | ⟨h1, h2⟩
  · exact absurd (eq_of_subset_of_card_le hj (by rw [card_Rset, h7])) (hne j)
  · have hs := card_eq_split Y
    have hW : (Y ∩ Wset 1 6).card = 1 := by
      rw [Wset_one_six, inter_singleton_of_mem (flat7_zero hc hY h7), card_singleton]
    rw [card_inter_Rset, hW]
    fin_cases k <;> simp <;> omega

section perm

variable {c0 : Finset (Finset (Pt 1 6))} {σ : Equiv.Perm (Pt 1 6)}

lemma flat_G (hσ : mapBlocks σ c0 ∈ Ccon 1 6) (k : Fin 3) :
    IsFlat c0 ((Rset 1 6 k).image σ.symm) := by
  have := IsFlat.mapBlocks_equiv σ.symm (flat_Rset (show 1 ≤ 1 by norm_num) hσ k)
  rwa [mapBlocks_symm_mapBlocks] at this

lemma card_G (k : Fin 3) : ((Rset 1 6 k).image σ.symm).card = 7 := by
  rw [card_image_of_injective _ σ.symm.injective, card_Rset]

lemma card_G_inter {i k : Fin 3} (hik : i ≠ k) :
    ((Rset 1 6 i).image σ.symm ∩ (Rset 1 6 k).image σ.symm).card = 1 :=
  card_image_Rset_inter σ.symm hik

lemma image_G (k : Fin 3) : ((Rset 1 6 k).image σ.symm).image σ = Rset 1 6 k := by
  rw [image_image]; simp

/-- Transport of `flat7_meet3` along `σ`. -/
lemma meet3_G (hσ : mapBlocks σ c0 ∈ Ccon 1 6) {Y : Finset (Pt 1 6)} (hY : IsFlat c0 Y)
    (h7 : Y.card = 7) (hne : ∀ k, Y ≠ (Rset 1 6 k).image σ.symm) (k : Fin 3) :
    (Y ∩ (Rset 1 6 k).image σ.symm).card = 3 := by
  have h1 := flat7_meet3 hσ (IsFlat.mapBlocks_equiv σ hY)
    (by rw [card_image_of_injective _ σ.injective, h7])
    (fun j hj => hne j (by rw [← hj, image_image]; simp)) k
  have e : (Y ∩ (Rset 1 6 k).image σ.symm).card = (Y.image σ ∩ Rset 1 6 k).card := by
    rw [← card_image_of_injective (Y ∩ (Rset 1 6 k).image σ.symm) σ.injective,
      image_inter_of_injOn _ _ σ.injective.injOn, image_G]
  rw [e, h1]

lemma A_sub_G (hc0 : c0 ∈ Ccon 1 6) (hσ : mapBlocks σ c0 ∈ Ccon 1 6) {A : Finset (Pt 1 6)}
    (hA : A ∈ c0) (hoA : Sum.inl 0 ∈ A) : ∃ k, A ⊆ (Rset 1 6 k).image σ.symm := by
  have hS := isSTS_of_mem_Ccon (show 1 ≤ 1 by norm_num) hc0
  obtain ⟨a, haA, hao⟩ : ∃ a ∈ A, a ≠ Sum.inl 0 := by
    by_contra h
    push_neg at h
    have : A ⊆ {Sum.inl 0} := fun x hx => mem_singleton.2 (h x hx)
    have := card_le_card this
    rw [hS.1 A hA, card_singleton] at this
    omega
  obtain ⟨k, hk⟩ : ∃ k, σ a ∈ Rset 1 6 k := by
    rcases cover (σ a) with h | h | h | h
    · exact ⟨0, by rw [Rset_eq]; exact mem_union_left _ h⟩
    · exact ⟨0, by rw [Rset_eq]; exact mem_union_right _ h⟩
    · exact ⟨1, by rw [Rset_eq]; exact mem_union_right _ h⟩
    · exact ⟨2, by rw [Rset_eq]; exact mem_union_right _ h⟩
  refine ⟨k, IsFlat.subset_of_two hS (flat_G hσ k) hA hao haA hoA ?_ ?_⟩
  · exact mem_image.2 ⟨σ a, hk, by simp⟩
  · exact flat7_zero hc0 (flat_G hσ k) (card_G k)

end perm

/-- Each constructed system of order 19 is mapped onto a constructed system by at most
`4 · 3! · (6!)³` permutations. -/
theorem card_perm_Ccon19 {c0 : Finset (Finset (Pt 1 6))} (hc0 : c0 ∈ Ccon 1 6) :
    (univ.filter (fun σ : Equiv.Perm (Pt 1 6) => mapBlocks σ c0 ∈ Ccon 1 6)).card ≤
      24 * Nat.factorial 6 ^ 3 := by
  obtain ⟨S, hSdef⟩ : ∃ S, S = univ.filter (fun σ : Equiv.Perm (Pt 1 6) => mapBlocks σ c0 ∈ Ccon 1 6) :=
    ⟨_, rfl⟩
  rw [← hSdef]
  have hS := isSTS_of_mem_Ccon (show 1 ≤ 1 by norm_num) hc0
  -- a block through `0`
  obtain ⟨A, ⟨hA, hoA, -⟩, -⟩ := hS.2 (Sum.inl 0) (Sum.inr (0, 0)) (by simp)
  have hA3 : A.card = 3 := hS.1 A hA
  have memS : ∀ {σ}, σ ∈ S ↔ mapBlocks σ c0 ∈ Ccon 1 6 := by
    intro σ; simp [hSdef]
  obtain ⟨E, hEdef⟩ : ∃ E, E = (S.biUnion (fun σ => univ.image
      (fun k => (Rset 1 6 k).image σ.symm))).filter (fun Y => A ⊆ Y) := ⟨_, rfl⟩
  have memE : ∀ {Y}, Y ∈ E → A ⊆ Y ∧ ∃ σ ∈ S, ∃ k, Y = (Rset 1 6 k).image σ.symm := by
    intro Y hY
    simp only [hEdef, mem_filter, mem_biUnion, mem_image, mem_univ, true_and] at hY
    obtain ⟨⟨σ, hσ, k, rfl⟩, h⟩ := hY
    exact ⟨h, σ, hσ, k, rfl⟩
  -- covering
  have hcov : S ⊆ E.biUnion (fun Y => S.filter (fun σ => ∃ k, (Rset 1 6 k).image σ.symm = Y)) := by
    intro σ hσ
    obtain ⟨k, hk⟩ := A_sub_G hc0 (memS.1 hσ) hA hoA
    refine mem_biUnion.2 ⟨(Rset 1 6 k).image σ.symm, ?_, mem_filter.2 ⟨hσ, k, rfl⟩⟩
    simp only [hEdef, mem_filter, mem_biUnion, mem_image, mem_univ, true_and]
    exact ⟨⟨σ, hσ, k, rfl⟩, hk⟩
  -- fibre bound
  have hfib : ∀ Y ∈ E, (S.filter (fun σ => ∃ k, (Rset 1 6 k).image σ.symm = Y)).card ≤
      6 * Nat.factorial 6 ^ 3 := by
    intro Y hY
    obtain ⟨-, σ0, hσ0, k0, rfl⟩ := memE hY
    refine le_trans ?_ (card_perm_R (w := 1) (m := 6) (by norm_num) (by norm_num))
    refine card_le_card_of_injOn (fun σ => σ * σ0⁻¹) ?_ ?_
    · intro σ hσ
      simp only [coe_filter, Set.mem_setOf_eq] at hσ
      obtain ⟨hσS, k, hk⟩ := hσ
      have hσ' := memS.1 hσS
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      intro i
      obtain ⟨j, hj⟩ : ∃ j, (Rset 1 6 i).image σ0.symm = (Rset 1 6 j).image σ.symm := by
        by_contra hne
        push_neg at hne
        have h3 := meet3_G hσ' (flat_G (memS.1 hσ0) i) (card_G i) hne k
        rw [hk] at h3
        by_cases hik : i = k0
        · subst hik; exact hne k hk.symm
        · rw [card_G_inter hik] at h3; omega
      refine ⟨j, ?_⟩
      rw [Equiv.Perm.coe_mul, ← image_image, Equiv.Perm.inv_def, hj, image_G]
    · intro σ _ τ _ h
      simpa using h
  -- the distinguished flats pairwise meet in `A`
  have hpair : ∀ Y₁ ∈ E, ∀ Y₂ ∈ E, Y₁ ≠ Y₂ → Y₁ ∩ Y₂ = A := by
    intro Y₁ h₁ Y₂ h₂ hne
    obtain ⟨hA₁, σ1, hσ1, k1, rfl⟩ := memE h₁
    obtain ⟨hA₂, σ2, hσ2, k2, rfl⟩ := memE h₂
    have hne2 : ∀ k, (Rset 1 6 k2).image σ2.symm ≠ (Rset 1 6 k).image σ1.symm := by
      intro k hk
      by_cases hkk : k1 = k
      · subst hkk; exact hne hk.symm
      · have := card_le_card (subset_inter hA₁ (hk ▸ hA₂))
        rw [card_G_inter hkk, hA3] at this
        omega
    have h3 := meet3_G (memS.1 hσ1) (flat_G (memS.1 hσ2) k2) (card_G k2) hne2 k1
    rw [inter_comm] at h3
    exact (eq_of_subset_of_card_le (subset_inter hA₁ hA₂) (by rw [h3, hA3])).symm
  -- at most 4 distinguished flats
  have hE4 : E.card ≤ 4 := by
    have hdisj : (E : Set (Finset (Pt 1 6))).PairwiseDisjoint (fun Y => Y \ A) := by
      intro Y₁ h₁ Y₂ h₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have := hpair Y₁ (mem_coe.1 h₁) Y₂ (mem_coe.1 h₂) hne
      have hx : x ∈ Y₁ ∩ Y₂ := mem_inter.2 ⟨(mem_sdiff.1 hx1).1, (mem_sdiff.1 hx2).1⟩
      rw [this] at hx
      exact (mem_sdiff.1 hx1).2 hx
    have hcard := card_biUnion hdisj
    have hsum : ∑ Y ∈ E, (Y \ A).card = E.card * 4 := by
      rw [← smul_eq_mul, ← sum_const]
      refine sum_congr rfl (fun Y hY => ?_)
      obtain ⟨hAY, σ, -, k, rfl⟩ := memE hY
      rw [card_sdiff_of_subset hAY, card_G, hA3]
    have hsub : E.biUnion (fun Y => Y \ A) ⊆ univ \ A := by
      intro x hx
      obtain ⟨Y, -, hx⟩ := mem_biUnion.1 hx
      exact mem_sdiff.2 ⟨mem_univ _, (mem_sdiff.1 hx).2⟩
    have := card_le_card hsub
    rw [hcard, hsum, card_sdiff_of_subset (subset_univ _), card_univ, card_Pt, hA3] at this
    omega
  calc S.card ≤ _ := card_le_card hcov
    _ ≤ ∑ Y ∈ E, (S.filter (fun σ => ∃ k, (Rset 1 6 k).image σ.symm = Y)).card := card_biUnion_le
    _ ≤ ∑ _Y ∈ E, 6 * Nat.factorial 6 ^ 3 := sum_le_sum hfib
    _ = E.card * (6 * Nat.factorial 6 ^ 3) := by rw [sum_const, smul_eq_mul]
    _ ≤ 4 * (6 * Nat.factorial 6 ^ 3) := Nat.mul_le_mul_right _ hE4
    _ = 24 * Nat.factorial 6 ^ 3 := by ring

theorem theorem4_i_aux : (Ccon 1 6).card ≤ (24 * Nat.factorial 6 ^ 3) * N 19 := by
  have e : Pt 1 6 ≃ Fin 19 := Fintype.equivFinOfCardEq (by rw [card_Pt])
  exact card_le_mul_N e _ (fun c hc => isSTS_of_mem_Ccon (by norm_num) hc) _
    (fun c0 hc0 => card_perm_Ccon19 hc0)

/-- **Theorem 4 (i).** `N(19) ≥ 2450`. -/
theorem theorem4_i : 2450 ≤ N 19 := by
  have h1 := theorem4_i_aux
  rw [card_Ccon (by norm_num), card_Sys, lemma5_i] at h1
  have h2 := D7_ge
  have h3 : Nat.factorial 6 * Nat.factorial 5 * 9408 * 30 ^ 3 ≤
      Nat.factorial 6 * Nat.factorial 5 * 9408 * D (1 + 6) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 3)
  by_contra h
  push_neg at h
  have h4 := Nat.mul_le_mul_left (24 * Nat.factorial 6 ^ 3) (Nat.le_of_lt_succ h)
  simp only [Nat.factorial, Nat.succ_eq_add_one] at h1 h3 h4
  norm_num at h1 h3 h4
  omega

end STS
