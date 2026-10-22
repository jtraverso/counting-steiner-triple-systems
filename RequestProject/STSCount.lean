/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.STSKernel

/-!
# Lower bounds for `D v` from lists of permutations, checked by the kernel

Given an STS `ofTriples v base` and a list of permutations of `{0, …, v - 1}` (each encoded as a
natural number whose hexadecimal digit `i` is the image of `i`), `countCheck` verifies that the
permutations are valid and that the images of the STS are pairwise distinct; for the latter, an
injective code of the image (`stsCode`) is computed, and the list of codes is checked to be
strictly increasing. Then `D v` is at least the length of the list (`length_le_D_of_countCheck`).
-/

@[expose] public section

open Finset

namespace STS

/-- Hexadecimal digit `i` of `p`. -/
def hexDigit (p i : ℕ) : ℕ := (p >>> (4 * i)) % 16

/-- `p` encodes a permutation of `{0, …, v - 1}`. -/
def permOkH (v p : ℕ) : Bool :=
  Nat.beq ((List.range v).foldl (fun acc i => acc ||| 2 ^ hexDigit p i) 0) (2 ^ v - 1)

/-- A code of the image of the triple system `base` under the permutation encoded by `p`: bit
`m` is set iff `m` is the bit mask of an image block. -/
def stsCode (base : List (ℕ × ℕ × ℕ)) (p : ℕ) : ℕ :=
  base.foldl (fun acc t => acc ||| 2 ^ (2 ^ hexDigit p t.1 ||| 2 ^ hexDigit p t.2.1 ||| 2 ^ hexDigit p t.2.2)) 0

/-- The list is strictly increasing. -/
def strictIncr : List ℕ → Bool
  | a :: b :: l => Nat.blt a b && strictIncr (b :: l)
  | _ => true

/-- The full check. -/
def countCheck (v : ℕ) (base : List (ℕ × ℕ × ℕ)) (perms : List ℕ) : Bool :=
  stsOK v base && perms.all (permOkH v) && strictIncr (perms.map (stsCode base))

/-- The map of `Fin v` encoded by `p`. -/
def decF (v p : ℕ) : Fin v → Fin v := fun i => ⟨hexDigit p i % v, Nat.mod_lt _ (by have := i.2; omega)⟩

lemma strictIncr_sound : ∀ l : List ℕ, strictIncr l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictIncr, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := strictIncr_sound (b :: l) h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.1 hx with e | hx
    · rw [e]; exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hx)

lemma permOkH_spec {v p : ℕ} (h : permOkH v p = true) :
    (∀ i < v, hexDigit p i < v) ∧ (∀ t < v, ∃ i < v, hexDigit p i = t) := by
  unfold permOkH at h
  rw [Nat.beq_eq] at h
  have key : ∀ k, ((List.range v).foldl (fun acc i => acc ||| 2 ^ hexDigit p i) 0).testBit k =
      (List.range v).any (fun i => decide (hexDigit p i = k)) := by
    intro k
    rw [testBit_foldl _ (fun i k => decide (hexDigit p i = k))]
    · simp
    · intro acc a k
      rw [Nat.testBit_or, Nat.testBit_two_pow]
  rw [h] at key
  constructor
  · intro i hi
    have := key (hexDigit p i)
    rw [Nat.testBit_two_pow_sub_one] at this
    have h2 : (List.range v).any (fun i' => decide (hexDigit p i' = hexDigit p i)) = true :=
      List.any_eq_true.2 ⟨i, List.mem_range.2 hi, by simp⟩
    rw [h2] at this
    simpa using this
  · intro t ht
    have := key t
    rw [Nat.testBit_two_pow_sub_one] at this
    simp only [ht, decide_true] at this
    obtain ⟨i, hi, hit⟩ := List.any_eq_true.1 this.symm
    exact ⟨i, List.mem_range.1 hi, by simpa using hit⟩

lemma decF_val {v p : ℕ} (h : permOkH v p = true) (i : Fin v) : (decF v p i : ℕ) = hexDigit p i := by
  simp only [decF]
  exact Nat.mod_eq_of_lt ((permOkH_spec h).1 i i.2)

lemma decF_bijective {v p : ℕ} (h : permOkH v p = true) : Function.Bijective (decF v p) := by
  have hs : Function.Surjective (decF v p) := by
    intro t
    obtain ⟨i, hi, hit⟩ := (permOkH_spec h).2 t t.2
    exact ⟨⟨i, hi⟩, Fin.ext (by rw [decF_val h]; exact hit)⟩
  exact (Fintype.bijective_iff_surjective_and_card _).2 ⟨hs, rfl⟩

lemma triOk_of_stsOK {v : ℕ} {l : List (ℕ × ℕ × ℕ)} (h : stsOK v l = true) :
    ∀ t ∈ l, triOk v t = true := by
  unfold stsOK at h
  rw [Bool.and_eq_true] at h
  cases hc : pairCover v l 0 with
  | none => rw [hc] at h; simp at h
  | some m => exact (pairCover_spec v l 0 m hc).1

lemma testBit_stsCode {v : ℕ} {base : List (ℕ × ℕ × ℕ)} (hb : ∀ t ∈ base, triOk v t = true)
    {p : ℕ} (hp : permOkH v p = true) (m : ℕ) :
    (stsCode base p).testBit m = true ↔
      ∃ A ∈ mapBlocks (decF v p) (ofTriples v base), ∀ z, m.testBit z = true ↔ ∃ x ∈ A, (x : ℕ) = z := by
  unfold stsCode
  rw [testBit_foldl _ (fun t m => decide
    ((2 ^ hexDigit p t.1 ||| 2 ^ hexDigit p t.2.1 ||| 2 ^ hexDigit p t.2.2) = m))]
  · simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(tripleBlock v t).image (decF v p), mem_image.2 ⟨tripleBlock v t, mem_ofTriples.2 ⟨t, ht, rfl⟩, rfl⟩,
        ?_⟩
      intro z
      obtain ⟨ha, hb', hc, -⟩ := (triOk_iff v t).1 (hb t ht)
      simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
        mem_image, mem_tripleBlock]
      constructor
      · rintro ((e | e) | e)
        · exact ⟨_, ⟨⟨t.1, ha⟩, Or.inl rfl, rfl⟩, by rw [decF_val hp]; exact e⟩
        · exact ⟨_, ⟨⟨t.2.1, hb'⟩, Or.inr (Or.inl rfl), rfl⟩, by rw [decF_val hp]; exact e⟩
        · exact ⟨_, ⟨⟨t.2.2, hc⟩, Or.inr (Or.inr rfl), rfl⟩, by rw [decF_val hp]; exact e⟩
      · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
        rw [decF_val hp]
        rcases hy with e | e | e <;> simp [e]
    · rintro ⟨A, hA, hAm⟩
      obtain ⟨A0, hA0, rfl⟩ := mem_image.1 hA
      obtain ⟨t, ht, rfl⟩ := mem_ofTriples.1 hA0
      refine ⟨t, ht, ?_⟩
      apply Nat.eq_of_testBit_eq
      intro z
      obtain ⟨ha, hb', hc, -⟩ := (triOk_iff v t).1 (hb t ht)
      have e := hAm z
      rw [Bool.eq_iff_iff, e]
      simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
        mem_image, mem_tripleBlock]
      constructor
      · rintro ((e | e) | e)
        · exact ⟨_, ⟨⟨t.1, ha⟩, Or.inl rfl, rfl⟩, by rw [decF_val hp]; exact e⟩
        · exact ⟨_, ⟨⟨t.2.1, hb'⟩, Or.inr (Or.inl rfl), rfl⟩, by rw [decF_val hp]; exact e⟩
        · exact ⟨_, ⟨⟨t.2.2, hc⟩, Or.inr (Or.inr rfl), rfl⟩, by rw [decF_val hp]; exact e⟩
      · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
        rw [decF_val hp]
        rcases hy with e | e | e <;> simp [e]
  · intro acc a i
    rw [Nat.testBit_or, Nat.testBit_two_pow]

lemma length_le_D {v : ℕ} (Ls : List (Finset (Finset (Fin v)))) (h1 : ∀ B ∈ Ls, IsSTS B)
    (h2 : Ls.Nodup) : Ls.length ≤ D v := by
  classical
  rw [← List.toFinset_card_of_nodup h2, D]
  have := Nat.card_le_card_of_injective
    (fun B : Ls.toFinset => (⟨B.1, h1 B.1 (List.mem_toFinset.1 B.2)⟩ : STSOn v))
    (fun B B' h => Subtype.ext (by simpa using congrArg Subtype.val h))
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this

/-- **`D v` is at least the length of a checked list of permutations.** -/
theorem length_le_D_of_countCheck {v : ℕ} {base : List (ℕ × ℕ × ℕ)} {perms : List ℕ}
    (h : countCheck v base perms = true) : perms.length ≤ D v := by
  unfold countCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hs, hp⟩, hi⟩ := h
  have hb := triOk_of_stsOK hs
  have hS := isSTS_of_stsOK hs
  let B : ℕ → Finset (Finset (Fin v)) := fun p => mapBlocks (decF v p) (ofTriples v base)
  have hlen : (perms.map B).length = perms.length := List.length_map _
  rw [← hlen]
  apply length_le_D
  · intro X hX
    obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hX
    exact isSTS_mapBlocks_equiv (Equiv.ofBijective _ (decF_bijective (hp p hp'))) hS
  · have hpw := strictIncr_sound _ hi
    rw [List.pairwise_map] at hpw
    rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hpw
    intro p q hpm hqm hlt hBpq
    have : stsCode base p = stsCode base q := by
      apply Nat.eq_of_testBit_eq
      intro m
      rw [Bool.eq_iff_iff, testBit_stsCode hb (hp p hpm), testBit_stsCode hb (hp q hqm)]
      simp only [B] at hBpq
      rw [hBpq]
    omega

end STS
