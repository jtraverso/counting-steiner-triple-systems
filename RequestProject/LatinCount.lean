/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Defs

/-!
# Counting Latin squares row by row

`Ext n S r` is the set of sequences of `r` permutations ("rows") of `Fin n` such that in every
column `j` the entries are distinct and avoid the set `S j`. Its cardinality `E n S r` satisfies
a recursion (`E_succ`), is invariant under permuting columns and relabelling symbols
(`E_transform`), and `L n = E n ∅ n` (`L_eq_E`).
-/

@[expose] public section

open Finset

namespace STS

/-- Sequences of `r` rows extending a partial Latin rectangle with column sets `S`. -/
def Ext (n : ℕ) (S : Fin n → Finset (Fin n)) (r : ℕ) : Type :=
  {rows : Fin r → Equiv.Perm (Fin n) //
    (∀ j, Function.Injective (fun i => rows i j)) ∧ ∀ i j, rows i j ∉ S j}

instance (n : ℕ) (S : Fin n → Finset (Fin n)) (r : ℕ) : Finite (Ext n S r) :=
  Subtype.finite

/-- The number of ways to extend by `r` rows. -/
noncomputable def E (n : ℕ) (S : Fin n → Finset (Fin n)) (r : ℕ) : ℕ := Nat.card (Ext n S r)

/-- Adding a row `σ` to the column sets `S`. -/
def addRow {n : ℕ} (S : Fin n → Finset (Fin n)) (σ : Equiv.Perm (Fin n)) :
    Fin n → Finset (Fin n) := fun j => insert (σ j) (S j)

lemma E_zero (n : ℕ) (S : Fin n → Finset (Fin n)) : E n S 0 = 1 := by
  unfold E
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨Fin.elim0, fun j => fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, ?_⟩
  intro x; apply Subtype.ext; funext i; exact Fin.elim0 i

/-- The equivalence behind the recursion for `E`. -/
def extSuccEquiv (n : ℕ) (S : Fin n → Finset (Fin n)) (r : ℕ) :
    Ext n S (r + 1) ≃ Σ σ : {σ : Equiv.Perm (Fin n) // ∀ j, σ j ∉ S j}, Ext n (addRow S σ.1) r where
  toFun x := ⟨⟨x.1 0, fun j => x.2.2 0 j⟩, ⟨Fin.tail x.1, fun j i i' h => by
      exact Fin.succ_injective _ (x.2.1 j h), fun i j => by
      simp only [addRow, mem_insert, not_or, Fin.tail]
      refine ⟨fun h => ?_, x.2.2 i.succ j⟩
      exact Fin.succ_ne_zero i (x.2.1 j h)⟩⟩
  invFun y := ⟨Fin.cons y.1.1 y.2.1, fun j => by
      intro i i' h
      refine Fin.cases (motive := fun i => ∀ i', (Fin.cons y.1.1 y.2.1 : Fin (r+1) → _) i j =
        (Fin.cons y.1.1 y.2.1 : Fin (r+1) → _) i' j → i = i') ?_ ?_ i i' h
      · intro i'
        refine Fin.cases ?_ ?_ i'
        · intro _; rfl
        · intro k hk
          simp only [Fin.cons_zero, Fin.cons_succ] at hk
          exact absurd hk.symm (fun h => (mem_insert.not.1 (y.2.2.2 k j)) (Or.inl h))
      · intro k i'
        refine Fin.cases ?_ ?_ i'
        · intro hk
          simp only [Fin.cons_zero, Fin.cons_succ] at hk
          exact absurd hk (fun h => (mem_insert.not.1 (y.2.2.2 k j)) (Or.inl h))
        · intro k' hk
          simp only [Fin.cons_succ] at hk
          exact congrArg Fin.succ (y.2.2.1 j hk), fun i j => by
      refine Fin.cases ?_ ?_ i
      · simpa using y.1.2 j
      · intro k
        simp only [Fin.cons_succ]
        exact fun h => y.2.2.2 k j (mem_insert_of_mem h)⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    rcases y with ⟨⟨σ, hσ⟩, ⟨rows, hrows⟩⟩
    rfl

lemma E_succ (n : ℕ) (S : Fin n → Finset (Fin n)) (r : ℕ) :
    E n S (r + 1) = ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ j, σ j ∉ S j),
      E n (addRow S σ) r := by
  classical
  unfold E
  rw [Nat.card_congr (extSuccEquiv n S r), Nat.card_sigma]
  exact (Finset.sum_subtype (univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ j, σ j ∉ S j))
    (fun σ => by simp) (fun σ => Nat.card (Ext n (addRow S σ) r))).symm

/-- Permuting the columns by `π` and relabelling the symbols by `τ`. -/
def transform {n : ℕ} (S : Fin n → Finset (Fin n)) (π τ : Equiv.Perm (Fin n)) :
    Fin n → Finset (Fin n) := fun j => (S (π j)).map τ.toEmbedding

lemma E_le_transform (n : ℕ) (S : Fin n → Finset (Fin n)) (π τ : Equiv.Perm (Fin n)) (r : ℕ) :
    E n S r ≤ E n (transform S π τ) r := by
  unfold E
  refine Nat.card_le_card_of_injective
    (fun x => ⟨fun i => (π.trans (x.1 i)).trans τ, fun j i i' h => ?_, fun i j => ?_⟩) ?_
  · simp only [Equiv.trans_apply, EmbeddingLike.apply_eq_iff_eq] at h
    exact x.2.1 (π j) h
  · simp only [transform, Equiv.trans_apply, mem_map_equiv, Equiv.symm_apply_apply]
    exact x.2.2 i (π j)
  · intro x y h
    apply Subtype.ext; funext i
    have := congrFun (congrArg Subtype.val h) i
    ext j
    have h2 := congrArg (fun f : Equiv.Perm (Fin n) => f (π.symm j)) this
    simp at h2; rw [h2]

lemma transform_transform {n : ℕ} (S : Fin n → Finset (Fin n)) (π τ : Equiv.Perm (Fin n)) :
    transform (transform S π τ) π.symm τ.symm = S := by
  funext j
  ext x
  simp [transform, mem_map_equiv]

lemma E_transform (n : ℕ) (S : Fin n → Finset (Fin n)) (π τ : Equiv.Perm (Fin n)) (r : ℕ) :
    E n (transform S π τ) r = E n S r := by
  refine le_antisymm ?_ (E_le_transform n S π τ r)
  have := E_le_transform n (transform S π τ) π.symm τ.symm r
  rwa [transform_transform] at this

/-- `L(n)` is the number of ways to fill an empty `n × n` array row by row. -/
theorem L_eq_E (n : ℕ) : L n = E n (fun _ => ∅) n := by
  unfold L E
  refine Nat.card_congr
    { toFun := fun l => ⟨fun i => Equiv.ofBijective (l.1 i) (l.2.1 i),
        fun j => (l.2.2 j).1, fun i j => by simp⟩
      invFun := fun x => ⟨fun i j => x.1 i j, fun i => (x.1 i).bijective,
        fun j => (Finite.injective_iff_bijective).1 (x.2.1 j)⟩
      left_inv := fun l => rfl
      right_inv := fun x => by apply Subtype.ext; funext i; ext j; rfl }

end STS
