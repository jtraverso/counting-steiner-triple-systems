/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Basic
public import RequestProject.NatBits

/-!
# A kernel-friendly checker for Steiner triple systems given by lists of triples

`stsOK v l` checks, with natural-number bit operations only, that the triples of `l` consist of
distinct points of `{0, …, v - 1}` and cover every pair of points exactly once (a pair `{x, y}`
with `x < y` is recorded as bit `64 x + y` of a pair-coverage mask). It is proved sound with
respect to `IsSTS` (`isSTS_of_stsOK`), so explicit systems can be checked by `decide +kernel`.
-/

@[expose] public section

open Finset

namespace STS

/-! ### The checker -/

/-- The index of the pair `{x, y}`. -/
def pidx (x y : ℕ) : ℕ := bif Nat.blt x y then 64 * x + y else 64 * y + x

/-- The pair-coverage mask of a triple. -/
def tmask (t : ℕ × ℕ × ℕ) : ℕ :=
  2 ^ pidx t.1 t.2.1 ||| 2 ^ pidx t.1 t.2.2 ||| 2 ^ pidx t.2.1 t.2.2

/-- A triple of distinct points of `{0, …, v - 1}`. -/
def triOk (v : ℕ) (t : ℕ × ℕ × ℕ) : Bool :=
  Nat.blt t.1 v && Nat.blt t.2.1 v && Nat.blt t.2.2 v && !Nat.beq t.1 t.2.1 &&
    !Nat.beq t.1 t.2.2 && !Nat.beq t.2.1 t.2.2

/-- Accumulating the pair-coverage masks of the triples, failing if a pair is covered twice. -/
def pairCover (v : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → Option ℕ
  | [], acc => some acc
  | t :: l, acc =>
    bif triOk v t && Nat.beq (acc &&& tmask t) 0 then pairCover v l (acc ||| tmask t) else none

/-- The mask of all pairs of points of `{0, …, v - 1}`. -/
def fullMask (v : ℕ) : ℕ :=
  (List.range v).foldl (fun acc y => (List.range y).foldl (fun acc x => acc ||| 2 ^ (64 * x + y))
    acc) 0

/-- The Steiner triple system check. -/
def stsOK (v : ℕ) (l : List (ℕ × ℕ × ℕ)) : Bool :=
  Nat.ble v 64 &&
    match pairCover v l 0 with
    | some m => Nat.beq m (fullMask v)
    | none => false

/-! ### Soundness -/

lemma pidx_eq (x y : ℕ) : pidx x y = if x < y then 64 * x + y else 64 * y + x := by
  unfold pidx
  by_cases h : x < y
  · have : Nat.blt x y = true := by rw [Nat.blt_eq]; exact h
    simp [this, h]
  · have : Nat.blt x y = false := by rw [← Bool.not_eq_true, Nat.blt_eq]; exact h
    simp [this, h]

lemma pidx_comm (x y : ℕ) : pidx x y = pidx y x := by
  rw [pidx_eq, pidx_eq]; split_ifs <;> omega

lemma pidx_inj {x y a b : ℕ} (hx : x < 64) (hy : y < 64) (ha : a < 64) (hb : b < 64)
    (hxy : x ≠ y) (hab : a ≠ b) (h : pidx x y = pidx a b) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  rw [pidx_eq, pidx_eq] at h
  split_ifs at h <;> omega

lemma testBit_tmask (t : ℕ × ℕ × ℕ) (i : ℕ) :
    (tmask t).testBit i = true ↔
      i = pidx t.1 t.2.1 ∨ i = pidx t.1 t.2.2 ∨ i = pidx t.2.1 t.2.2 := by
  simp only [tmask, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((h | h) | h) <;> simp [h]
  · rintro (h | h | h) <;> simp [h]

lemma triOk_iff (v : ℕ) (t : ℕ × ℕ × ℕ) :
    triOk v t = true ↔ t.1 < v ∧ t.2.1 < v ∧ t.2.2 < v ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧
      t.2.1 ≠ t.2.2 := by
  simp only [triOk, Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq]
  have e : ∀ a b : ℕ, Nat.beq a b = false ↔ a ≠ b := by
    intro a b; rw [← Bool.not_eq_true, Nat.beq_eq]
  simp only [e]
  tauto

lemma pairCover_spec (v : ℕ) : ∀ (l : List (ℕ × ℕ × ℕ)) (acc m : ℕ), pairCover v l acc = some m →
    (∀ t ∈ l, triOk v t = true) ∧
    (∀ i, m.testBit i = true ↔ acc.testBit i = true ∨ ∃ t ∈ l, (tmask t).testBit i = true) ∧
    (∀ t ∈ l, ∀ i, (tmask t).testBit i = true → acc.testBit i = false) ∧
    (∀ t ∈ l, ∀ t' ∈ l, t ≠ t' → ∀ i, (tmask t).testBit i = true → (tmask t').testBit i = false)
  | [], acc, m, h => by
    simp only [pairCover, Option.some.injEq] at h
    subst h
    simp
  | t :: l, acc, m, h => by
    simp only [pairCover] at h
    cases hc : (triOk v t && Nat.beq (acc &&& tmask t) 0) with
    | false => rw [hc] at h; simp at h
    | true =>
      rw [hc] at h
      simp only [cond_true] at h
      simp only [Bool.and_eq_true, Nat.beq_eq] at hc
      obtain ⟨ht, hdisj⟩ := hc
      have hd : ∀ i, (tmask t).testBit i = true → acc.testBit i = false := by
        intro i hi
        have := congrArg (fun z => z.testBit i) hdisj
        simp only [Nat.testBit_and, Nat.zero_testBit, hi, Bool.and_true] at this
        exact this
      obtain ⟨h1, h2, h3, h4⟩ := pairCover_spec v l _ _ h
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t' ht'
        rcases List.mem_cons.1 ht' with e | ht'
        · rw [e]; exact ht
        · exact h1 t' ht'
      · intro i
        rw [h2 i, Nat.testBit_or, Bool.or_eq_true]
        constructor
        · rintro ((hb | hb) | ⟨t', ht', hb⟩)
          · exact Or.inl hb
          · exact Or.inr ⟨t, by simp, hb⟩
          · exact Or.inr ⟨t', by simp [ht'], hb⟩
        · rintro (hb | ⟨t', ht', hb⟩)
          · exact Or.inl (Or.inl hb)
          · rcases List.mem_cons.1 ht' with e | ht'
            · rw [e] at hb; exact Or.inl (Or.inr hb)
            · exact Or.inr ⟨t', ht', hb⟩
      · intro t' ht' i hi
        rcases List.mem_cons.1 ht' with e | ht'
        · rw [e] at hi; exact hd i hi
        · have := h3 t' ht' i hi
          rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
          exact this.1
      · intro t1 ht1 t2 ht2 hne i hi
        rcases List.mem_cons.1 ht1 with e1 | ht1 <;> rcases List.mem_cons.1 ht2 with e2 | ht2
        · exact absurd (e1.trans e2.symm) hne
        · rw [e1] at hi
          cases h' : (tmask t2).testBit i with
          | false => rfl
          | true =>
            have := h3 t2 ht2 i h'
            rw [Nat.testBit_or, hi, Bool.or_true] at this
            exact absurd this (by simp)
        · rw [e2]
          have := h3 t1 ht1 i hi
          rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
          exact this.2
        · exact h4 t1 ht1 t2 ht2 hne i hi

lemma testBit_fullMask (v i : ℕ) :
    (fullMask v).testBit i = true ↔ ∃ x y, x < y ∧ y < v ∧ i = 64 * x + y := by
  unfold fullMask
  rw [testBit_foldl _ (fun y i => (List.range y).any (fun x => decide (64 * x + y = i)))]
  · simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_range,
      decide_eq_true_eq]
    constructor
    · rintro ⟨y, hy, x, hx, rfl⟩; exact ⟨x, y, hx, hy, rfl⟩
    · rintro ⟨x, y, hx, hy, rfl⟩; exact ⟨y, hy, x, hx, rfl⟩
  · intro acc y i
    rw [testBit_foldl _ (fun x i => decide (64 * x + y = i))]
    intro acc x i
    rw [Nat.testBit_or, Nat.testBit_two_pow]

/-- The block of `Fin v` described by a triple. -/
def tripleBlock (v : ℕ) (t : ℕ × ℕ × ℕ) : Finset (Fin v) :=
  univ.filter (fun x : Fin v => x.val = t.1 ∨ x.val = t.2.1 ∨ x.val = t.2.2)

lemma mem_ofTriples {v : ℕ} {L : List (ℕ × ℕ × ℕ)} {A : Finset (Fin v)} :
    A ∈ ofTriples v L ↔ ∃ t ∈ L, tripleBlock v t = A := by
  simp [ofTriples, tripleBlock]

lemma mem_tripleBlock {v : ℕ} {t : ℕ × ℕ × ℕ} {x : Fin v} :
    x ∈ tripleBlock v t ↔ x.val = t.1 ∨ x.val = t.2.1 ∨ x.val = t.2.2 := by
  simp [tripleBlock]

lemma card_tripleBlock {v : ℕ} {t : ℕ × ℕ × ℕ} (ht : triOk v t = true) : (tripleBlock v t).card = 3 := by
  rw [triOk_iff] at ht
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := ht
  rw [card_eq_three]
  refine ⟨⟨t.1, ha⟩, ⟨t.2.1, hb⟩, ⟨t.2.2, hc⟩, ?_, ?_, ?_, ?_⟩
  · simpa [Fin.ext_iff] using hab
  · simpa [Fin.ext_iff] using hac
  · simpa [Fin.ext_iff] using hbc
  · ext x
    simp [tripleBlock, Fin.ext_iff]

lemma tmask_of_mem {v : ℕ} {t : ℕ × ℕ × ℕ} {x y : Fin v} (hxy : x ≠ y) (hx : x ∈ tripleBlock v t)
    (hy : y ∈ tripleBlock v t) : (tmask t).testBit (pidx x y) = true := by
  rw [testBit_tmask]
  rw [mem_tripleBlock] at hx hy
  have hxy' : (x : ℕ) ≠ y := fun h => hxy (Fin.ext h)
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;>
    simp only [hx, hy, pidx_comm t.2.1 t.1, pidx_comm t.2.2 t.1, pidx_comm t.2.2 t.2.1,
      true_or, or_true] <;> omega

lemma mem_of_tmask {v : ℕ} (hv : v ≤ 64) {t : ℕ × ℕ × ℕ} (ht : triOk v t = true) {x y : Fin v}
    (hxy : x ≠ y) (h : (tmask t).testBit (pidx x y) = true) : x ∈ tripleBlock v t ∧ y ∈ tripleBlock v t := by
  rw [triOk_iff] at ht
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := ht
  have hxy' : (x : ℕ) ≠ y := fun h => hxy (Fin.ext h)
  have hx := x.2
  have hy := y.2
  rw [testBit_tmask] at h
  rw [mem_tripleBlock, mem_tripleBlock]
  rcases h with h | h | h
  · rcases pidx_inj (by omega) (by omega) (by omega) (by omega) hxy' hab h with h | h <;> omega
  · rcases pidx_inj (by omega) (by omega) (by omega) (by omega) hxy' hac h with h | h <;> omega
  · rcases pidx_inj (by omega) (by omega) (by omega) (by omega) hxy' hbc h with h | h <;> omega

/-- **Soundness of the checker.** -/
theorem isSTS_of_stsOK {v : ℕ} {l : List (ℕ × ℕ × ℕ)} (h : stsOK v l = true) :
    IsSTS (ofTriples v l) := by
  unfold stsOK at h
  rw [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨hv, h⟩ := h
  cases hc : pairCover v l 0 with
  | none => rw [hc] at h; simp at h
  | some m =>
    rw [hc] at h
    simp only [Nat.beq_eq] at h
    subst h
    obtain ⟨h1, h2, -, h4⟩ := pairCover_spec v l 0 _ hc
    refine ⟨?_, ?_⟩
    · intro A hA
      obtain ⟨t, ht, rfl⟩ := mem_ofTriples.1 hA
      exact card_tripleBlock (h1 t ht)
    · intro x y hxy
      have hxy' : (x : ℕ) ≠ y := fun h => hxy (Fin.ext h)
      have hfull : (fullMask v).testBit (pidx x y) = true := by
        rw [testBit_fullMask, pidx_eq]
        split_ifs with h
        · exact ⟨x, y, h, y.2, rfl⟩
        · exact ⟨y, x, by omega, x.2, rfl⟩
      obtain ⟨t, ht, htb⟩ := ((h2 _).1 hfull).resolve_left (by simp)
      obtain ⟨hxt, hyt⟩ := mem_of_tmask hv (h1 t ht) hxy htb
      refine ⟨tripleBlock v t, ⟨mem_ofTriples.2 ⟨t, ht, rfl⟩, hxt, hyt⟩, ?_⟩
      rintro A ⟨hA, hxA, hyA⟩
      obtain ⟨t', ht', rfl⟩ := mem_ofTriples.1 hA
      by_cases htt : t' = t
      · rw [htt]
      · exfalso
        have := h4 t' ht' t ht htt _ (tmask_of_mem hxy hxA hyA)
        rw [htb] at this
        exact absurd this (by simp)

/-! ### The fixed Fano plane -/

/-- The blocks of `fano` as triples. -/
def fanoT : List (ℕ × ℕ × ℕ) := [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6),
  (2, 4, 5)]

lemma fano_eq : fano = ofTriples 7 fanoT := by decide +kernel

lemma image_tripleBlock {v : ℕ} (h : 7 ≤ v) {t : ℕ × ℕ × ℕ} (ht : triOk 7 t = true) :
    (tripleBlock 7 t).image (Fin.castLE h) = tripleBlock v t := by
  rw [triOk_iff] at ht
  ext x
  simp only [mem_image, mem_tripleBlock]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨⟨x, by omega⟩, by simpa using hx, Fin.ext rfl⟩

lemma fanoIn_subset_of {v : ℕ} (h : 7 ≤ v) {l : List (ℕ × ℕ × ℕ)}
    (hl : fanoT.all (fun t => l.contains t) = true) : fanoIn v ⊆ ofTriples v l := by
  intro A hA
  rw [fanoIn, dite_eq_left h, mapBlocks, fano_eq, mem_image] at hA
  obtain ⟨A0, hA0, rfl⟩ := hA
  obtain ⟨t, ht, rfl⟩ := mem_ofTriples.1 hA0
  have htri : triOk 7 t = true := by
    revert t; decide
  rw [image_tripleBlock h htri]
  exact mem_ofTriples.2 ⟨t, by simpa using List.all_eq_true.1 hl t ht, rfl⟩

end STS
