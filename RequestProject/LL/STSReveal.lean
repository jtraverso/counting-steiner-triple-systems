/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LL.Order

/-!
# Steiner triple systems as Steiner quasigroups; the revealing argument

A Steiner triple system on `Fin n` is encoded by the map `T` with `T a b` the third point of
the block through `a ≠ b` (and `T a a = a`): this is the variable `X_{a,b}` of the paper.

`NvalSTS lam nu T i j` is the random variable `N_{i,j}` of Section 3 of the paper (for the
orders given by the labels `lam`, `nu`): it is `1` unless the event `F_{i,j}`
(`i ≪ j`, `i ≪ k`, `{i,j} ≺ {i,k}` where `k = X_{i,j}`) occurs, and otherwise it counts `k`
together with the vertices `t` that are not ruled out by the previously revealed entries.

`reveal_sts` is the key combinatorial fact: among all systems that agree with `T` on the
pairs revealed before `(i, j)`, the entry at `(i, j)` takes at most `NvalSTS lam nu T i j`
values.
-/

@[expose] public section

open Finset

namespace LinialLuria

variable {n L : ℕ}

/-- `T` is a Steiner quasigroup: the "third point" map of a Steiner triple system. -/
def IsSQ (T : Fin n → Fin n → Fin n) : Prop :=
  (∀ a, T a a = a) ∧ ∀ a b, a ≠ b → T a b ≠ a ∧ T a b ≠ b ∧ T b a = T a b ∧ T a (T a b) = b

section SQ

variable {T : Fin n → Fin n → Fin n} (hT : IsSQ T)
include hT

lemma IsSQ.diag (a : Fin n) : T a a = a := hT.1 a
lemma IsSQ.ne_left {a b : Fin n} (h : a ≠ b) : T a b ≠ a := (hT.2 a b h).1
lemma IsSQ.ne_right {a b : Fin n} (h : a ≠ b) : T a b ≠ b := (hT.2 a b h).2.1
lemma IsSQ.comm (a b : Fin n) : T b a = T a b := by
  by_cases h : a = b
  · subst h; rfl
  · exact (hT.2 a b h).2.2.1
lemma IsSQ.invol (a b : Fin n) : T a (T a b) = b := by
  by_cases h : a = b
  · subst h; rw [hT.diag, hT.diag]
  · exact (hT.2 a b h).2.2.2
lemma IsSQ.inj {a b c : Fin n} (h : T a b = T a c) : b = c := by
  rw [← hT.invol a b, h, hT.invol]

end SQ

/-- The random variable `N_{i,j}` of the paper (Steiner triple system case). -/
def NvalSTS (lam nu : Fin n → Fin L) (T : Fin n → Fin n → Fin n) (i j : Fin n) : ℕ :=
  if vpos lam i < vpos lam j ∧ vpos lam i < vpos lam (T i j) ∧ vpos nu j < vpos nu (T i j) then
    1 + (univ.filter (fun t => t ≠ i ∧ t ≠ j ∧ t ≠ T i j ∧ vpos lam i < vpos lam t ∧
      vpos lam i < vpos lam (T i t) ∧ vpos lam i < vpos lam (T j t) ∧
      vpos nu j < vpos nu t ∧ vpos nu j < vpos nu (T i t))).card
  else 1

lemma one_le_NvalSTS (lam nu : Fin n → Fin L) (T : Fin n → Fin n → Fin n) (i j : Fin n) :
    1 ≤ NvalSTS lam nu T i j := by
  unfold NvalSTS; split_ifs <;> omega

/-- **Revealing lemma** (Steiner triple systems). -/
theorem reveal_sts (lam nu : Fin n → Fin L) {T : Fin n → Fin n → Fin n} (hT : IsSQ T)
    {i j : Fin n} (hij : i ≠ j) (P : Finset (Fin n → Fin n → Fin n))
    (hP : ∀ T' ∈ P, IsSQ T' ∧
      ∀ a b, a ≠ b → ekey lam nu (a, b) < ekey lam nu (i, j) → T' a b = T a b) :
    (P.image (fun T' => T' i j)).card ≤ NvalSTS lam nu T i j := by
  set k := T i j with hk
  have hki : k ≠ i := hT.ne_left hij
  have hkj : k ≠ j := hT.ne_right hij
  have hTik : T i k = j := hT.invol i j
  have hTki : T k i = j := by rw [hT.comm]; exact hTik
  unfold NvalSTS
  rw [← hk]
  split_ifs with hF
  · obtain ⟨h1, h2, h3⟩ := hF
    rw [add_comm]
    refine (card_le_card ?_).trans (card_insert_le k _)
    intro x hx
    obtain ⟨T', hT'P, rfl⟩ := mem_image.1 hx
    obtain ⟨hT', ag⟩ := hP T' hT'P
    set t := T' i j with ht
    rw [mem_insert]
    by_cases htk : t = k
    · exact Or.inl htk
    right
    have hti : t ≠ i := hT'.ne_left hij
    have htj : t ≠ j := hT'.ne_right hij
    have hT'it : T' i t = j := hT'.invol i j
    have hT'jt : T' j t = i := by
      rw [ht, ← hT'.comm i j, hT'.invol]
    -- `T i t = j` forces `t = k`
    have key0 : T i t ≠ j := by
      intro h; apply htk; rw [hk, ← h, hT.invol]
    have hit : vpos lam i < vpos lam t := by
      by_contra hc
      have hlt : vpos lam t < vpos lam i := by
        have := vpos_ne lam hti; omega
      have := ag t i hti (ekey_lt_of_before lam nu t i i j (Or.inl hlt) h1)
      rw [hT'.comm, hT'it, hT.comm] at this
      exact key0 this.symm
    set a := T i t with ha
    have hai : a ≠ i := hT.ne_left (Ne.symm hti)
    have haj : a ≠ j := key0
    have hia : vpos lam i < vpos lam a := by
      by_contra hc
      have hlt : vpos lam a < vpos lam i := by
        have := vpos_ne lam hai; omega
      have := ag a i hai (ekey_lt_of_before lam nu a i i j (Or.inl hlt) h1)
      rw [hT'.comm, hT.comm, ha, hT.invol] at this
      apply haj
      rw [← hT'.invol i a, this, hT'it]
    set b := T j t with hb
    have hbi : b ≠ i := by
      intro h; apply htk
      rw [hk, ← hT.comm i j, ← h, hb, hT.invol]
    have hbj : b ≠ j := hT.ne_left (Ne.symm htj)
    have hib : vpos lam i < vpos lam b := by
      by_contra hc
      have hlt : vpos lam b < vpos lam i := by
        have := vpos_ne lam hbi; omega
      have := ag b j hbj (ekey_lt_of_before lam nu b j i j (Or.inl hlt) h1)
      rw [hT'.comm, hT.comm, hb, hT.invol] at this
      apply hbi
      rw [← hT'.invol j b, this, hT'jt]
    have hnt : vpos nu j < vpos nu t := by
      by_contra hc
      have hlt : vpos nu t < vpos nu j := by
        have := vpos_ne nu htj; omega
      have := ag i t (Ne.symm hti) (ekey_lt_star lam nu i j t h1 hit hlt)
      rw [hT'it] at this
      exact key0 this.symm
    have hna : vpos nu j < vpos nu a := by
      by_contra hc
      have hlt : vpos nu a < vpos nu j := by
        have := vpos_ne nu haj; omega
      have := ag i a (Ne.symm hai) (ekey_lt_star lam nu i j a h1 hia hlt)
      have e1 : T i a = t := by rw [ha, hT.invol]
      rw [e1] at this
      apply haj
      rw [← hT'.invol i a, this, hT'it]
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨hti, htj, htk, hit, hia, hib, hnt, hna⟩
  · refine (card_le_card (t := {k}) ?_).trans (by simp)
    intro x hx
    obtain ⟨T', hT'P, rfl⟩ := mem_image.1 hx
    obtain ⟨hT', ag⟩ := hP T' hT'P
    rw [mem_singleton]
    rcases lt_or_gt_of_ne (vpos_ne lam hij) with h1 | h1
    · by_cases h2 : vpos lam i < vpos lam k
      · have h3 : vpos nu k < vpos nu j := by
          have := vpos_ne nu hkj
          have : ¬ vpos nu j < vpos nu k := fun h => hF ⟨h1, h2, h⟩
          omega
        have := ag i k (Ne.symm hki) (ekey_lt_star lam nu i j k h1 h2 h3)
        rw [hTik] at this
        rw [← this, hT'.invol]
      · have h3 : vpos lam k < vpos lam i := by
          have := vpos_ne lam hki; omega
        have := ag k i hki (ekey_lt_of_before lam nu k i i j (Or.inl h3) h1)
        rw [hTki, hT'.comm] at this
        rw [← this, hT'.invol]
    · have := ag j i (Ne.symm hij) (ekey_lt_swap lam nu i j h1)
      rw [hT'.comm, hT.comm] at this
      exact this

end LinialLuria
