/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LL.Order

/-!
# 1-factorizations: the revealing argument

A 1-factorization of `K_n` is viewed (as in the paper) as a proper edge colouring of `K_n` with
the `n - 1` colours `Fin (n - 1)`, encoded by the symmetric map `c` with `c a b` the colour of
the edge `{a, b}` (the variable `X_{a,b}` of the paper; the diagonal values are irrelevant).

`NvalOF lam nu c i j` is the random variable `N_{i,j}` of Section 2: it is `1` unless `i ≪ j`,
and otherwise it counts the colour `X_{i,j}` together with the colours `X_{i,a}` that are not
ruled out by the previously revealed entries.
-/

@[expose] public section

open Finset

namespace LinialLuria

variable {n L : ℕ}

/-- `c` is a proper edge colouring of `K_n` with the colours `Fin (n - 1)` (only the
off-diagonal values are constrained). -/
def IsOF (c : Fin n → Fin n → Fin (n - 1)) : Prop :=
  (∀ a b, c b a = c a b) ∧ ∀ a b b', a ≠ b → a ≠ b' → c a b = c a b' → b = b'

section OF

variable {c : Fin n → Fin n → Fin (n - 1)} (hc : IsOF c)
include hc

lemma IsOF.comm (a b : Fin n) : c b a = c a b := hc.1 a b

lemma IsOF.inj {a b b' : Fin n} (hb : a ≠ b) (hb' : a ≠ b') (h : c a b = c a b') : b = b' :=
  hc.2 a b b' hb hb' h

/-- Every colour appears at every vertex. -/
lemma IsOF.surj (a : Fin n) (κ : Fin (n - 1)) : ∃ b, b ≠ a ∧ c a b = κ := by
  have hinj : Set.InjOn (c a) ((univ.erase a : Finset (Fin n)) : Set (Fin n)) := by
    intro b hb b' hb' h
    simp only [coe_erase, coe_univ, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff,
      true_and] at hb hb'
    exact hc.inj (Ne.symm hb) (Ne.symm hb') h
  have hcard : ((univ.erase a).image (c a)).card = Fintype.card (Fin (n - 1)) := by
    rw [card_image_of_injOn hinj, card_erase_of_mem (mem_univ a), card_univ,
      Fintype.card_fin, Fintype.card_fin]
  have huniv := eq_univ_of_card _ hcard
  have : κ ∈ (univ.erase a).image (c a) := by rw [huniv]; exact mem_univ κ
  obtain ⟨b, hb, rfl⟩ := mem_image.1 this
  exact ⟨b, ne_of_mem_erase hb, rfl⟩

end OF

/-- The random variable `N_{i,j}` of the paper (1-factorization case). -/
def NvalOF (lam nu : Fin n → Fin L) (c : Fin n → Fin n → Fin (n - 1)) (i j : Fin n) : ℕ :=
  if vpos lam i < vpos lam j then
    1 + (univ.filter (fun a => a ≠ i ∧ a ≠ j ∧ vpos lam i < vpos lam a ∧
      vpos nu j < vpos nu a ∧ ∀ t, vpos lam t < vpos lam i → c t j ≠ c i a)).card
  else 1

/-- **Revealing lemma** (1-factorizations). -/
theorem reveal_of (lam nu : Fin n → Fin L) {c : Fin n → Fin n → Fin (n - 1)} (hc : IsOF c)
    {i j : Fin n} (hij : i ≠ j) (P : Finset (Fin n → Fin n → Fin (n - 1)))
    (hP : ∀ c' ∈ P, IsOF c' ∧
      ∀ a b, a ≠ b → ekey lam nu (a, b) < ekey lam nu (i, j) → c' a b = c a b) :
    (P.image (fun c' => c' i j)).card ≤ NvalOF lam nu c i j := by
  unfold NvalOF
  split_ifs with h1
  · rw [add_comm]
    refine (card_le_card ?_).trans ((card_insert_le (c i j) _).trans
      (Nat.add_le_add_right (card_image_le (f := c i)) 1))
    intro x hx
    obtain ⟨c', hc'P, rfl⟩ := mem_image.1 hx
    obtain ⟨hc', ag⟩ := hP c' hc'P
    obtain ⟨a, hai, ha⟩ := hc.surj i (c' i j)
    rw [mem_insert]
    by_cases haj : a = j
    · left; rw [← ha, haj]
    right
    rw [mem_image]
    refine ⟨a, ?_, ha⟩
    have hia : vpos lam i < vpos lam a := by
      by_contra hcon
      have hlt : vpos lam a < vpos lam i := by
        have := vpos_ne lam hai; omega
      have := ag a i hai (ekey_lt_of_before lam nu a i i j (Or.inl hlt) h1)
      rw [hc'.comm, hc.comm, ha] at this
      exact haj (hc'.inj (Ne.symm hai) hij this)
    have hna : vpos nu j < vpos nu a := by
      by_contra hcon
      have hlt : vpos nu a < vpos nu j := by
        have := vpos_ne nu haj; omega
      have := ag i a (Ne.symm hai) (ekey_lt_star lam nu i j a h1 hia hlt)
      rw [ha] at this
      exact haj (hc'.inj (Ne.symm hai) hij this)
    have ht : ∀ t, vpos lam t < vpos lam i → c t j ≠ c i a := by
      intro t ht hct
      have htj : t ≠ j := by
        intro h; rw [h] at ht; omega
      have hti : t ≠ i := by
        intro h; rw [h] at ht; omega
      have := ag t j htj (ekey_lt_of_before lam nu t j i j (Or.inl ht) h1)
      rw [hct, ha, ← hc'.comm t j, hc'.comm j i] at this
      exact hti (hc'.inj (Ne.symm htj) (Ne.symm hij) this)
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨hai, haj, hia, hna, ht⟩
  · refine (card_le_card (t := {c i j}) ?_).trans (by simp)
    intro x hx
    obtain ⟨c', hc'P, rfl⟩ := mem_image.1 hx
    obtain ⟨hc', ag⟩ := hP c' hc'P
    rw [mem_singleton]
    have h2 : vpos lam j < vpos lam i := by
      have := vpos_ne lam hij; omega
    have := ag j i (Ne.symm hij) (ekey_lt_swap lam nu i j h2)
    rw [hc'.comm, hc.comm] at this
    exact this

end LinialLuria
