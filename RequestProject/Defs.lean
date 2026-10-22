/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Basic definitions for *Nonisomorphic Steiner Triple Systems* (R. M. Wilson, 1974)

* `STS.IsSTS B` : the family of blocks `B` is a Steiner triple system on the point type.
* `STS.N v` : the number of pairwise nonisomorphic STS's of order `v`.
* `STS.D v` : the number of distinct STS's on the fixed `v`-set `Fin v`.
* `STS.IsLatin l`, `STS.L n` : Latin squares of order `n` and their number.
* `STS.fano`, `STS.D7 v` : a fixed STS of order 7 and the number of STS's on `Fin v`
  containing it (on the points `0, …, 6`).
* `STS.vdWPC` : the van der Waerden permanent conjecture (used only as a hypothesis,
  exactly as in the paper).
-/

@[expose] public section

open Finset

namespace STS

variable {α : Type*} [DecidableEq α]

/-- `B` is a Steiner triple system on the point type `α`: every block is a 3-subset, and
any two distinct points lie in exactly one block. -/
def IsSTS (B : Finset (Finset α)) : Prop :=
  (∀ A ∈ B, A.card = 3) ∧ ∀ x y : α, x ≠ y → ∃! A, A ∈ B ∧ x ∈ A ∧ y ∈ A

/-- The image of a family of blocks under a map of points. -/
def mapBlocks {β : Type*} [DecidableEq β] (f : α → β) (B : Finset (Finset α)) :
    Finset (Finset β) :=
  B.image (fun A => A.image f)

/-- Two families of blocks on `Fin v` are isomorphic if some permutation of the points
maps the blocks of the first onto the blocks of the second. -/
def Iso {v : ℕ} (B₁ B₂ : Finset (Finset (Fin v))) : Prop :=
  ∃ σ : Equiv.Perm (Fin v), mapBlocks σ B₁ = B₂

/-- The STS's on the point set `Fin v`. -/
abbrev STSOn (v : ℕ) := {B : Finset (Finset (Fin v)) // IsSTS B}

lemma mapBlocks_id (B : Finset (Finset α)) : mapBlocks id B = B := by
  simp [mapBlocks]

omit [DecidableEq α] in
lemma mapBlocks_comp {β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ] (f : α → β) (g : β → γ)
    (B : Finset (Finset α)) : mapBlocks g (mapBlocks f B) = mapBlocks (g ∘ f) B := by
  simp only [mapBlocks, Finset.image_image]
  congr 1
  funext A
  simp [Finset.image_image]

/-- Isomorphism is an equivalence relation on STS's of order `v`. -/
instance isoSetoid (v : ℕ) : Setoid (STSOn v) where
  r B₁ B₂ := Iso B₁.1 B₂.1
  iseqv := by
    refine ⟨fun B => ⟨1, by simpa using mapBlocks_id B.1⟩, ?_, ?_⟩
    · rintro B₁ B₂ ⟨σ, h⟩
      refine ⟨σ⁻¹, ?_⟩
      rw [← h, mapBlocks_comp]
      convert mapBlocks_id B₁.1
      funext x; simp
    · rintro B₁ B₂ B₃ ⟨σ, h⟩ ⟨τ, h'⟩
      refine ⟨τ * σ, ?_⟩
      rw [← h', ← h, mapBlocks_comp]
      rfl

/-- `N v`: the number of pairwise nonisomorphic Steiner triple systems of order `v`. -/
noncomputable def N (v : ℕ) : ℕ := Nat.card (Quotient (isoSetoid v))

/-- `D v`: the number of distinct classes of 3-subsets `B` of the fixed `v`-set `Fin v`
such that `(Fin v, B)` is an STS. -/
noncomputable def D (v : ℕ) : ℕ := Nat.card (STSOn v)

/-- A Latin square of order `n`: a map `l : rows × columns → symbols` (all three sets being
`Fin n`) such that each row and each column contains each symbol exactly once. -/
def IsLatin {n : ℕ} (l : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Function.Bijective (l i)) ∧ ∀ j, Function.Bijective (fun i => l i j)

/-- `L n`: the number of Latin squares of order `n`. -/
noncomputable def L (n : ℕ) : ℕ := Nat.card {l : Fin n → Fin n → Fin n // IsLatin l}

/-- A fixed Steiner triple system of order 7 (the Fano plane) on `Fin 7`. -/
def fano : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

/-- The fixed STS of order 7 placed on the points `0, …, 6` of `Fin v` (empty if `v < 7`). -/
def fanoIn (v : ℕ) : Finset (Finset (Fin v)) :=
  if h : 7 ≤ v then mapBlocks (Fin.castLE h) fano else ∅

/-- `D7 v`: the number of STS's on `Fin v` containing the fixed STS of order 7 on the
7-subset `{0, …, 6}`. -/
noncomputable def D7 (v : ℕ) : ℕ :=
  Nat.card {B : Finset (Finset (Fin v)) // IsSTS B ∧ fanoIn v ⊆ B}

/-- The van der Waerden permanent conjecture: the permanent of a doubly stochastic matrix
of order `n` is at least `n! / n^n`. -/
def vdWPC : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ), M ∈ doublyStochastic ℝ (Fin n) →
    (Nat.factorial n : ℝ) / (n : ℝ) ^ n ≤ M.permanent

/-- `v` is admissible: `v ≡ 1` or `3 (mod 6)`. -/
def Admissible (v : ℕ) : Prop := v % 6 = 1 ∨ v % 6 = 3

end STS
