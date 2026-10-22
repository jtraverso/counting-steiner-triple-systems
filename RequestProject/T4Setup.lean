/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Core
public import RequestProject.IsoCount

/-!
# Setup for Theorem 4

The point set `Pt w m = Fin w ⊕ (Fin 3 × Fin m)` (with `w ≤ 1`) is partitioned into
`W = Wset` and `Zᵢ = Zset i`; `Rᵢ = Rset i = W ∪ Zᵢ`. The systems `Φ(B, l)` of the construction
of Lemma 3 (with `G = ∅`) form the finite set `Ccon w m`.
-/

@[expose] public section

open Finset

namespace STS.T4

variable {w m : ℕ}

/-- The point set. -/
abbrev Pt (w m : ℕ) := Fin w ⊕ (Fin 3 × Fin m)

/-- The set `W`. -/
def Wset (w m : ℕ) : Finset (Pt w m) := univ.image Sum.inl

/-- The set `Zᵢ`. -/
def Zset (w m : ℕ) (i : Fin 3) : Finset (Pt w m) := univ.image (fun b => Sum.inr (i, b))

/-- The set `Rᵢ = W ∪ Zᵢ`, the image of `ιᵢ`. -/
def Rset (w m : ℕ) (i : Fin 3) : Finset (Pt w m) := univ.image (Construction.ι i)

lemma mem_Wset (x : Pt w m) : x ∈ Wset w m ↔ x.isLeft := by
  cases x <;> simp [Wset]

lemma mem_Zset (x : Pt w m) (i : Fin 3) : x ∈ Zset w m i ↔ ∃ b, x = Sum.inr (i, b) := by
  cases x with
  | inl a => simp [Zset]
  | inr p => simp [Zset, Prod.ext_iff, eq_comm]

lemma Rset_eq (i : Fin 3) : Rset w m i = Wset w m ∪ Zset w m i := by
  ext x
  cases x with
  | inl a => simp [Rset, Wset, Zset, Construction.ι]
  | inr p =>
    simp only [Rset, Wset, Zset, Construction.ι, mem_image, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨y, hy⟩
      cases y with
      | inl a => simp at hy
      | inr b => right; exact ⟨b, by simpa using hy⟩
    · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
      · simp at ha
      · exact ⟨Sum.inr b, by simpa using hb⟩

lemma card_Wset : (Wset w m).card = w := by
  rw [Wset, card_image_of_injective _ Sum.inl_injective, card_univ, Fintype.card_fin]

lemma card_Zset (i : Fin 3) : (Zset w m i).card = m := by
  rw [Zset, card_image_of_injective, card_univ, Fintype.card_fin]
  intro a b h; simpa using h

lemma disjoint_WZ (i : Fin 3) : Disjoint (Wset w m) (Zset w m i) := by
  rw [Finset.disjoint_left]
  intro x hx hz
  rw [mem_Wset] at hx
  obtain ⟨b, rfl⟩ := (mem_Zset x i).1 hz
  simp at hx

lemma disjoint_ZZ {i j : Fin 3} (hij : i ≠ j) : Disjoint (Zset w m i) (Zset w m j) := by
  rw [Finset.disjoint_left]
  intro x hx hz
  obtain ⟨b, rfl⟩ := (mem_Zset _ i).1 hx
  obtain ⟨b', hb'⟩ := (mem_Zset _ j).1 hz
  simp only [Sum.inr.injEq, Prod.mk.injEq] at hb'
  exact hij hb'.1

lemma cover (x : Pt w m) : x ∈ Wset w m ∨ x ∈ Zset w m 0 ∨ x ∈ Zset w m 1 ∨ x ∈ Zset w m 2 := by
  cases x with
  | inl a => left; simp [mem_Wset]
  | inr p =>
    obtain ⟨i, b⟩ := p
    right
    fin_cases i
    · left; exact (mem_Zset _ _).2 ⟨b, rfl⟩
    · right; left; exact (mem_Zset _ _).2 ⟨b, rfl⟩
    · right; right; exact (mem_Zset _ _).2 ⟨b, rfl⟩

lemma univ_eq : (univ : Finset (Pt w m)) = Wset w m ∪ Zset w m 0 ∪ Zset w m 1 ∪ Zset w m 2 := by
  ext x; simp only [mem_univ, mem_union, true_iff]
  rcases cover x with h | h | h | h <;> simp [h]

lemma card_Pt : Fintype.card (Pt w m) = w + 3 * m := by
  simp [Fintype.card_sum, Fintype.card_prod]

lemma Rset_inter {i j : Fin 3} (hij : i ≠ j) : Rset w m i ∩ Rset w m j = Wset w m := by
  rw [Rset_eq, Rset_eq, ← union_inter_distrib_left, Finset.disjoint_iff_inter_eq_empty.1 (disjoint_ZZ hij), union_empty]

lemma Rset_sdiff (i : Fin 3) : Rset w m i \ Wset w m = Zset w m i := by
  rw [Rset_eq, union_sdiff_left, sdiff_eq_self_of_disjoint (disjoint_WZ i).symm]

lemma card_Rset (i : Fin 3) : (Rset w m i).card = w + m := by
  rw [Rset_eq, card_union_of_disjoint (disjoint_WZ i), card_Wset, card_Zset]

lemma card_eq_split (Y : Finset (Pt w m)) :
    Y.card = (Y ∩ Wset w m).card + (Y ∩ Zset w m 0).card + (Y ∩ Zset w m 1).card +
      (Y ∩ Zset w m 2).card := by
  have hY : Y = Y ∩ Wset w m ∪ Y ∩ Zset w m 0 ∪ Y ∩ Zset w m 1 ∪ Y ∩ Zset w m 2 := by
    rw [← inter_union_distrib_left, ← inter_union_distrib_left, ← inter_union_distrib_left,
      ← univ_eq, inter_univ]
  conv_lhs => rw [hY]
  have d01 := disjoint_ZZ (w := w) (m := m) (show (0 : Fin 3) ≠ 1 by decide)
  have d02 := disjoint_ZZ (w := w) (m := m) (show (0 : Fin 3) ≠ 2 by decide)
  have d12 := disjoint_ZZ (w := w) (m := m) (show (1 : Fin 3) ≠ 2 by decide)
  rw [card_union_of_disjoint, card_union_of_disjoint, card_union_of_disjoint]
  · exact Disjoint.mono inter_subset_right inter_subset_right (disjoint_WZ 0)
  · rw [disjoint_union_left]
    exact ⟨Disjoint.mono inter_subset_right inter_subset_right (disjoint_WZ 1),
      Disjoint.mono inter_subset_right inter_subset_right d01⟩
  · rw [disjoint_union_left, disjoint_union_left]
    exact ⟨⟨Disjoint.mono inter_subset_right inter_subset_right (disjoint_WZ 2),
      Disjoint.mono inter_subset_right inter_subset_right d02⟩,
      Disjoint.mono inter_subset_right inter_subset_right d12⟩

/-! ### The constructed systems -/

/-- Latin squares of order `m`. -/
abbrev Lat (m : ℕ) := {l : Fin m → Fin m → Fin m // IsLatin l}

/-- STS's on `Fin w ⊕ Fin m`. -/
abbrev Sys (w m : ℕ) := {B : Finset (Finset (Fin w ⊕ Fin m)) // IsSTS B}

open Classical in
/-- The set of systems `Φ(B, l)`. -/
noncomputable def Ccon (w m : ℕ) : Finset (Finset (Finset (Pt w m))) :=
  univ.image (fun p : Lat m × (Fin 3 → Sys w m) => Construction.Φ (fun i => (p.2 i).1) p.1.1)

lemma mem_Ccon {c : Finset (Finset (Pt w m))} (hc : c ∈ Ccon w m) :
    ∃ B : Fin 3 → Finset (Finset (Fin w ⊕ Fin m)), ∃ l, (∀ i, IsSTS (B i)) ∧ IsLatin l ∧
      c = Construction.Φ B l := by
  classical
  unfold Ccon at hc
  obtain ⟨p, -, rfl⟩ := mem_image.1 hc
  exact ⟨_, _, fun i => (p.2 i).2, p.1.2, rfl⟩

lemma coversW_empty (hw : w ≤ 1) :
    Construction.CoversW (∅ : Finset (Finset (Fin w ⊕ Fin m))) := by
  intro a a' h
  exact absurd (Fin.ext (by omega)) h

lemma isSTS_of_mem_Ccon (hw : w ≤ 1) {c : Finset (Finset (Pt w m))} (hc : c ∈ Ccon w m) :
    IsSTS c := by
  obtain ⟨B, l, hB, hl, rfl⟩ := mem_Ccon hc
  exact Construction.isSTS_Φ (fun i => ⟨hB i, empty_subset _⟩) (coversW_empty hw) hl

lemma card_Ccon (hw : w ≤ 1) : (Ccon w m).card = L m * Nat.card (Sys w m) ^ 3 := by
  classical
  unfold Ccon
  rw [card_image_of_injective, card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    L, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rintro ⟨l, B⟩ ⟨l', B'⟩ h
  obtain ⟨h1, h2⟩ := Construction.Φ_injective (fun i => ⟨(B i).2, empty_subset _⟩)
    (fun i => ⟨(B' i).2, empty_subset _⟩) (coversW_empty hw) h
  have hl : l = l' := Subtype.ext h2
  have hB : B = B' := funext (fun i => Subtype.ext (congrFun h1 i))
  rw [hl, hB]

lemma card_Sys : Nat.card (Sys w m) = D (w + m) := by
  have := DSub_equiv (finSumFinEquiv (m := w) (n := m)) ∅
  simp only [mapBlocks, image_empty] at this
  unfold DSub at this
  rw [D]
  rw [← Nat.card_congr (Equiv.subtypeEquivRight (fun B => by simp) :
      {B : Finset (Finset (Fin (w + m))) // IsSTS B ∧ ∅ ⊆ B} ≃ STSOn (w + m)), this]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun B => by simp))

lemma T_inter_Rset (l : Fin m → Fin m → Fin m) (xy : Fin m × Fin m) (i : Fin 3) :
    (Construction.T (W := Fin w) l xy ∩ Rset w m i).card = 1 := by
  rw [card_eq_one]
  fin_cases i
  · refine ⟨Sum.inr (0, xy.1), ?_⟩
    ext z; simp only [Construction.T, Rset_eq, mem_inter, mem_insert, mem_singleton, mem_union,
      mem_Wset, mem_Zset]
    constructor
    · rintro ⟨h1 | h1 | h1, h2⟩ <;> subst h1 <;> simp_all
    · rintro rfl; simp
  · refine ⟨Sum.inr (1, xy.2), ?_⟩
    ext z; simp only [Construction.T, Rset_eq, mem_inter, mem_insert, mem_singleton, mem_union,
      mem_Wset, mem_Zset]
    constructor
    · rintro ⟨h1 | h1 | h1, h2⟩ <;> subst h1 <;> simp_all
    · rintro rfl; simp
  · refine ⟨Sum.inr (2, l xy.1 xy.2), ?_⟩
    ext z; simp only [Construction.T, Rset_eq, mem_inter, mem_insert, mem_singleton, mem_union,
      mem_Wset, mem_Zset]
    constructor
    · rintro ⟨h1 | h1 | h1, h2⟩ <;> subst h1 <;> simp_all
    · rintro rfl; simp

lemma image_ι_subset_Rset (A : Finset (Fin w ⊕ Fin m)) (j : Fin 3) :
    A.image (Construction.ι j) ⊆ Rset w m j :=
  image_subset_image (subset_univ _)

/-- The sets `Rᵢ` are flats of every constructed system. -/
lemma flat_Rset (hw : w ≤ 1) {c : Finset (Finset (Pt w m))} (hc : c ∈ Ccon w m) (i : Fin 3) :
    IsFlat c (Rset w m i) := by
  obtain ⟨B, l, hB, hl, rfl⟩ := mem_Ccon hc
  intro A hA
  rcases Construction.mem_Φ.1 hA with ⟨j, A', hA', rfl⟩ | ⟨xy, rfl⟩
  · by_cases hij : j = i
    · subst hij
      right; right
      rw [inter_eq_left.2 (image_ι_subset_Rset A' j),
        card_image_of_injective _ (Construction.ι_injective j), (hB j).1 A' hA']
    · have hsub : A'.image (Construction.ι j) ∩ Rset w m i ⊆ Wset w m := by
        rw [← Rset_inter hij]
        exact inter_subset_inter_right (image_ι_subset_Rset A' j)
      have := card_le_card hsub
      rw [card_Wset] at this
      omega
  · right; left; exact T_inter_Rset l xy i

/-- Lemma 6 applied to the constructed systems. -/
lemma flat_dichotomy (hw : w ≤ 1) {c : Finset (Finset (Pt w m))} (hc : c ∈ Ccon w m)
    {Y : Finset (Pt w m)} (hY : IsFlat c Y) :
    (∃ i, Y ⊆ Rset w m i) ∨ ((Y ∩ Zset w m 0).card = (Y ∩ Zset w m 1).card ∧
      (Y ∩ Zset w m 1).card = (Y ∩ Zset w m 2).card) := by
  by_cases h : ∃ i, Y ⊆ Rset w m i
  · exact Or.inl h
  push_neg at h
  right
  have hF : ∀ i, IsFlat c (Wset w m ∪ Zset w m i) := fun i => by
    rw [← Rset_eq]; exact flat_Rset hw hc i
  refine lemma6 c (isSTS_of_mem_Ccon hw hc) (Wset w m) (Zset w m 0) (Zset w m 1) (Zset w m 2)
    (disjoint_WZ 0) (disjoint_WZ 1) (disjoint_WZ 2) (disjoint_ZZ (by decide))
    (disjoint_ZZ (by decide)) (disjoint_ZZ (by decide)) univ_eq.symm (hF 0) (hF 1) (hF 2) Y hY
    ?_ ?_ ?_
  · rw [← Rset_eq]; exact h 0
  · rw [← Rset_eq]; exact h 1
  · rw [← Rset_eq]; exact h 2

end STS.T4
