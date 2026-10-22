/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Defs

/-!
# Basic facts about Steiner triple systems used throughout
-/

@[expose] public section

open Finset

namespace STS

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma mem_mapBlocks_equiv (e : α ≃ β) (B : Finset (Finset α)) (A : Finset β) :
    A ∈ mapBlocks e B ↔ A.image e.symm ∈ B := by
  constructor
  · intro h
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.1 h
    rw [Finset.image_image]
    simpa using hA'
  · intro h
    refine Finset.mem_image.2 ⟨_, h, ?_⟩
    rw [Finset.image_image]
    simp

lemma isSTS_mapBlocks_equiv (e : α ≃ β) {B : Finset (Finset α)} (hB : IsSTS B) :
    IsSTS (mapBlocks e B) := by
  obtain ⟨h3, hu⟩ := hB
  refine ⟨?_, ?_⟩
  · intro A hA
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.1 hA
    rw [Finset.card_image_of_injective _ e.injective]
    exact h3 _ hA'
  · intro x y hxy
    obtain ⟨A, ⟨hA, hxA, hyA⟩, huniq⟩ := hu (e.symm x) (e.symm y) (by simpa using hxy)
    refine ⟨A.image e, ⟨Finset.mem_image_of_mem _ hA, ?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.2 ⟨_, hxA, by simp⟩
    · exact Finset.mem_image.2 ⟨_, hyA, by simp⟩
    · rintro A' ⟨hA', hx, hy⟩
      rw [mem_mapBlocks_equiv] at hA'
      have := huniq _ ⟨hA', Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hy⟩
      rw [← this, Finset.image_image]
      simp

lemma mapBlocks_symm_mapBlocks (e : α ≃ β) (B : Finset (Finset α)) :
    mapBlocks e.symm (mapBlocks e B) = B := by
  rw [mapBlocks_comp]
  convert mapBlocks_id B
  funext x; simp

lemma mapBlocks_subset_mapBlocks {f : α → β} {B₁ B₂ : Finset (Finset α)} (h : B₁ ⊆ B₂) :
    mapBlocks f B₁ ⊆ mapBlocks f B₂ :=
  Finset.image_subset_image h

instance (v : ℕ) : Finite (STSOn v) := inferInstance

/-- Inequality (2.1), left half. -/
lemma N_le_D' (v : ℕ) : N v ≤ D v :=
  Nat.card_le_card_of_surjective _ (Quotient.mk_surjective (s := isoSetoid v))

/-- Inequality (2.1), right half. -/
lemma D_le_factorial_mul_N' (v : ℕ) : D v ≤ v.factorial * N v := by
  classical
  let f : Equiv.Perm (Fin v) × Quotient (isoSetoid v) → STSOn v :=
    fun p => ⟨mapBlocks p.1 p.2.out.1, isSTS_mapBlocks_equiv p.1 p.2.out.2⟩
  have hf : Function.Surjective f := by
    intro B
    have h : (Quotient.mk (isoSetoid v) B).out ≈ B := Quotient.mk_out (s := isoSetoid v) B
    obtain ⟨σ, hσ⟩ := h
    exact ⟨(σ, Quotient.mk (isoSetoid v) B), Subtype.ext hσ⟩
  have := Nat.card_le_card_of_surjective f hf
  unfold D N
  refine this.trans ?_
  rw [Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin v), Fintype.card_fin]

/-- A decidable reformulation of `IsSTS` on a finite point set. -/
lemma isSTS_iff_card [Fintype α] (B : Finset (Finset α)) :
    IsSTS B ↔ (∀ A ∈ B, A.card = 3) ∧
      ∀ x y : α, x ≠ y → (B.filter (fun A => x ∈ A ∧ y ∈ A)).card = 1 := by
  unfold IsSTS
  refine and_congr Iff.rfl (forall_congr' fun x => forall_congr' fun y => imp_congr_right fun _ => ?_)
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨A, hA, hu⟩
    refine ⟨A, ?_⟩
    ext C
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hC; exact hu C hC
    · rintro rfl; exact hA
  · rintro ⟨A, hA⟩
    have hmem : A ∈ B.filter (fun A => x ∈ A ∧ y ∈ A) := by rw [hA]; exact Finset.mem_singleton_self A
    rw [Finset.mem_filter] at hmem
    refine ⟨A, ⟨hmem.1, hmem.2⟩, fun C hC => ?_⟩
    have : C ∈ B.filter (fun A => x ∈ A ∧ y ∈ A) := Finset.mem_filter.2 ⟨hC.1, hC.2⟩
    rw [hA] at this
    exact Finset.mem_singleton.1 this

/-- A Boolean test for being an STS (used to check explicit examples by evaluation). -/
def stsCheck [Fintype α] (B : Finset (Finset α)) : Bool :=
  decide (B.filter (fun A => A.card ≠ 3) = ∅) &&
    decide (∀ x y : α, x ≠ y → (B.filter (fun A => x ∈ A ∧ y ∈ A)).card = 1)

lemma isSTS_of_stsCheck [Fintype α] {B : Finset (Finset α)} (h : stsCheck B = true) :
    IsSTS B := by
  rw [isSTS_iff_card]
  unfold stsCheck at h
  rw [Bool.and_eq_true] at h
  refine ⟨fun A hA => ?_, of_decide_eq_true h.2⟩
  have h1 := of_decide_eq_true h.1
  rw [Finset.filter_eq_empty_iff] at h1
  simpa using h1 hA

/-- The family of blocks on `Fin v` described by a list of triples of natural numbers. -/
def ofTriples (v : ℕ) (L : List (ℕ × ℕ × ℕ)) : Finset (Finset (Fin v)) :=
  (L.map (fun t => Finset.univ.filter
    (fun x : Fin v => x.val = t.1 ∨ x.val = t.2.1 ∨ x.val = t.2.2))).toFinset

end STS
