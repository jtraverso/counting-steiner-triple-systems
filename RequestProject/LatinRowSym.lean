/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LatinCount

/-!
# Fixing the first entry of the next row

The rows of an extension can be permuted freely. Hence, if the column `c` still misses exactly
`r + 1` symbols and `a` is one of them, exactly a `1 / (r + 1)` fraction of the extensions by
`r + 1` rows have `a` in column `c` of their first row (`E_succ_fix`).
-/

@[expose] public section

open Finset

namespace STS

variable {n : ℕ}

/-- Permuting the rows of an extension. -/
def rowEquiv (S : Fin n → Finset (Fin n)) (r : ℕ) (τ : Equiv.Perm (Fin r)) :
    Ext n S r ≃ Ext n S r where
  toFun ρ := ⟨ρ.1 ∘ τ, fun j i i' h => τ.injective (ρ.2.1 j h), fun i j => ρ.2.2 (τ i) j⟩
  invFun ρ := ⟨ρ.1 ∘ τ.symm, fun j i i' h => τ.symm.injective (ρ.2.1 j h),
    fun i j => ρ.2.2 (τ.symm i) j⟩
  left_inv ρ := by apply Subtype.ext; funext i; simp
  right_inv ρ := by apply Subtype.ext; funext i; simp

lemma card_row_eq (S : Fin n → Finset (Fin n)) (r : ℕ) (c b : Fin n) (i : Fin (r + 1)) :
    Nat.card {ρ : Ext n S (r + 1) // ρ.1 i c = b} =
      Nat.card {ρ : Ext n S (r + 1) // ρ.1 0 c = b} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (rowEquiv S (r + 1) (Equiv.swap 0 i)) ?_)
  intro ρ
  change (ρ.1 i c = b) ↔ (ρ.1 ((Equiv.swap 0 i) 0) c = b)
  rw [Equiv.swap_apply_left]

lemma card_ext_eq_sum (S : Fin n → Finset (Fin n)) (r : ℕ) (c a : Fin n) (ha : a ∉ S c)
    (hcard : (S c).card + (r + 1) = n) :
    E n S (r + 1) = ∑ i : Fin (r + 1), Nat.card {ρ : Ext n S (r + 1) // ρ.1 i c = a} := by
  classical
  have hex : ∀ ρ : Ext n S (r + 1), ∃ i, ρ.1 i c = a := by
    intro ρ
    let col : Fin (r + 1) → Fin n := fun i => ρ.1 i c
    have hinj : Function.Injective col := ρ.2.1 c
    have hsub : univ.image col ⊆ (S c)ᶜ := by
      intro b hb
      obtain ⟨i, -, rfl⟩ := mem_image.1 hb
      exact mem_compl.2 (ρ.2.2 i c)
    have heq : univ.image col = (S c)ᶜ := by
      apply eq_of_subset_of_card_le hsub
      rw [card_compl, card_image_of_injective _ hinj, card_univ, Fintype.card_fin,
        Fintype.card_fin]
      omega
    have : a ∈ univ.image col := by rw [heq]; exact mem_compl.2 ha
    obtain ⟨i, -, hi⟩ := mem_image.1 this
    exact ⟨i, hi⟩
  unfold E
  rw [← Nat.card_sigma]
  symm
  refine Nat.card_eq_of_bijective (fun p => p.2.1) ⟨?_, ?_⟩
  · intro p q h
    apply Sigma.subtype_ext _ h
    have h1 := p.2.2
    have h2 := q.2.2
    simp only at h
    rw [h] at h1
    exact q.2.1.2.1 c (h1.trans h2.symm)
  · intro ρ
    obtain ⟨i, hi⟩ := hex ρ
    exact ⟨⟨i, ρ, hi⟩, rfl⟩

/-- The extensions whose first row has `a` in column `c`. -/
def extFixEquiv (S : Fin n → Finset (Fin n)) (r : ℕ) (c a : Fin n) :
    {ρ : Ext n S (r + 1) // ρ.1 0 c = a} ≃
      Σ σ : {σ : Equiv.Perm (Fin n) // (∀ j, σ j ∉ S j) ∧ σ c = a}, Ext n (addRow S σ.1) r where
  toFun ρ := ⟨⟨(extSuccEquiv n S r ρ.1).1.1, (extSuccEquiv n S r ρ.1).1.2, ρ.2⟩,
    (extSuccEquiv n S r ρ.1).2⟩
  invFun q := ⟨(extSuccEquiv n S r).symm ⟨⟨q.1.1, q.1.2.1⟩, q.2⟩, q.1.2.2⟩
  left_inv ρ := by
    apply Subtype.ext
    exact (extSuccEquiv n S r).symm_apply_apply ρ.1
  right_inv q := by
    rcases q with ⟨⟨σ, hσ1, hσ2⟩, x⟩
    rfl

lemma card_fix_eq_sum (S : Fin n → Finset (Fin n)) (r : ℕ) (c a : Fin n) :
    Nat.card {ρ : Ext n S (r + 1) // ρ.1 0 c = a} =
      ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => (∀ j, σ j ∉ S j) ∧ σ c = a),
        E n (addRow S σ) r := by
  classical
  rw [Nat.card_congr (extFixEquiv S r c a), Nat.card_sigma]
  exact (Finset.sum_subtype (univ.filter (fun σ : Equiv.Perm (Fin n) => (∀ j, σ j ∉ S j) ∧ σ c = a))
    (fun σ => by simp) (fun σ => Nat.card (Ext n (addRow S σ) r))).symm

/-- **Fixing the first entry of the next row.** -/
theorem E_succ_fix (S : Fin n → Finset (Fin n)) (r : ℕ) (c a : Fin n) (ha : a ∉ S c)
    (hcard : (S c).card + (r + 1) = n) :
    E n S (r + 1) = (r + 1) *
      ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => (∀ j, σ j ∉ S j) ∧ σ c = a),
        E n (addRow S σ) r := by
  rw [card_ext_eq_sum S r c a ha hcard, ← card_fix_eq_sum]
  simp only [card_row_eq S r c a]
  simp

end STS
