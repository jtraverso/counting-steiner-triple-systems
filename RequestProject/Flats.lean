/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Defs

/-!
# Flats and Lemma 6

* `STS.IsFlat` : flats (subsets meeting every block in 0, 1 or 3 points).
* `STS.lemma6` : Lemma 6 of the paper.
-/

@[expose] public section

open Finset

namespace STS

variable {α : Type*} [DecidableEq α]

/-- A subset `Z` of the points is a *flat* of the system with blocks `B` if every block meets
`Z` in 0, 1 or 3 points. -/
def IsFlat (B : Finset (Finset α)) (Z : Finset α) : Prop :=
  ∀ A ∈ B, (A ∩ Z).card = 0 ∨ (A ∩ Z).card = 1 ∨ (A ∩ Z).card = 3

lemma IsFlat.subset_of_two {B : Finset (Finset α)} (hB : IsSTS B) {Z : Finset α}
    (hZ : IsFlat B Z) {A : Finset α} (hA : A ∈ B) {a b : α} (hab : a ≠ b) (ha : a ∈ A)
    (hb : b ∈ A) (haZ : a ∈ Z) (hbZ : b ∈ Z) : A ⊆ Z := by
  have h2 : 2 ≤ (A ∩ Z).card := by
    have : ({a, b} : Finset α) ⊆ A ∩ Z := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [*]
    simpa [card_pair hab] using card_le_card this
  have h3 : (A ∩ Z).card = A.card := by
    rw [hB.1 A hA]; rcases hZ A hA with h | h | h <;> omega
  have := Finset.eq_of_subset_of_card_le inter_subset_left h3.ge
  rw [← this]; exact inter_subset_right

lemma third_point (A : Finset α) (hA3 : A.card = 3) (a b : α) (hab : a ≠ b) :
    ∃ c ∈ A, c ≠ a ∧ c ≠ b := by
  by_contra h
  push_neg at h
  have : A ⊆ {a, b} := fun c hc => by
    by_cases hca : c = a
    · simp [hca]
    · simp [h c hc hca]
  have := card_le_card this
  rw [card_pair hab] at this; omega

lemma card_four_le {A : Finset α} (hA : A.card = 3) {a b c d : α} (ha : a ∈ A) (hb : b ∈ A)
    (hc : c ∈ A) (hd : d ∈ A) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : False := by
  have : ({a, b, c, d} : Finset α) ⊆ A := by
    intro x hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h := card_le_card this
  rw [card_insert_of_notMem (by simp [hab, hac, had]), card_insert_of_notMem (by simp [hbc, hbd]),
    card_pair hcd] at h
  omega

section Lemma6

variable {B : Finset (Finset α)} (hB : IsSTS B) {W P Q R : Finset α}
  (hWP : Disjoint W P) (hWQ : Disjoint W Q) (hWR : Disjoint W R)
  (hPQ : Disjoint P Q) (hPR : Disjoint P R) (hQR : Disjoint Q R)
  (hcover : ∀ x, x ∈ W ∨ x ∈ P ∨ x ∈ Q ∨ x ∈ R)
  (hFP : IsFlat B (W ∪ P)) (hFQ : IsFlat B (W ∪ Q))
include hB hWP hWQ hWR hPQ hPR hQR hcover hFP hFQ

omit hWR hPR hQR in
lemma lemma6_third {A : Finset α} (hA : A ∈ B) {a b c : α} (ha : a ∈ A) (haP : a ∈ P)
    (hb : b ∈ A) (hbQ : b ∈ Q) (hc : c ∈ A) (hca : c ≠ a) (hcb : c ≠ b) : c ∈ R := by
  have hab : a ≠ b := fun h => Finset.disjoint_left.1 hPQ haP (h ▸ hbQ)
  rcases hcover c with h | h | h | h
  · have := IsFlat.subset_of_two hB hFP hA hca hc ha (mem_union_left _ h) (mem_union_right _ haP)
    rcases mem_union.1 (this hb) with h' | h'
    · exact absurd hbQ (Finset.disjoint_left.1 hWQ h')
    · exact absurd hbQ (Finset.disjoint_left.1 hPQ h')
  · have := IsFlat.subset_of_two hB hFP hA hca hc ha (mem_union_right _ h) (mem_union_right _ haP)
    rcases mem_union.1 (this hb) with h' | h'
    · exact absurd hbQ (Finset.disjoint_left.1 hWQ h')
    · exact absurd hbQ (Finset.disjoint_left.1 hPQ h')
  · have := IsFlat.subset_of_two hB hFQ hA hcb hc hb (mem_union_right _ h) (mem_union_right _ hbQ)
    rcases mem_union.1 (this ha) with h' | h'
    · exact absurd haP (Finset.disjoint_left.1 hWP h')
    · exact absurd h' (Finset.disjoint_left.1 hPQ haP)
  · exact h

omit hWR hPR hQR in
lemma lemma6_meets {Y : Finset α} (hY : IsFlat B Y) (hYP : ¬ Y ⊆ W ∪ P) (hYQ : ¬ Y ⊆ W ∪ Q) :
    ∃ x ∈ Y, x ∈ R := by
  by_contra hno
  push_neg at hno
  obtain ⟨y1, hy1Y, hy1⟩ := Finset.not_subset.1 hYP
  obtain ⟨y2, hy2Y, hy2⟩ := Finset.not_subset.1 hYQ
  simp only [mem_union, not_or] at hy1 hy2
  have hy1Q : y1 ∈ Q := by
    rcases hcover y1 with h | h | h | h
    · exact absurd h hy1.1
    · exact absurd h hy1.2
    · exact h
    · exact absurd h (hno y1 hy1Y)
  have hy2P : y2 ∈ P := by
    rcases hcover y2 with h | h | h | h
    · exact absurd h hy2.1
    · exact h
    · exact absurd h hy2.2
    · exact absurd h (hno y2 hy2Y)
  have hne : y2 ≠ y1 := fun h => Finset.disjoint_left.1 hPQ hy2P (h ▸ hy1Q)
  obtain ⟨A, ⟨hA, h2A, h1A⟩, -⟩ := hB.2 y2 y1 hne
  obtain ⟨c, hcA, hc2, hc1⟩ := third_point A (hB.1 A hA) y2 y1 hne
  have hAY := IsFlat.subset_of_two hB hY hA hne h2A h1A hy2Y hy1Y
  exact hno c (hAY hcA) (lemma6_third hB hWP hWQ hPQ hcover hFP hFQ hA h2A hy2P h1A hy1Q
    hcA hc2 hc1)

variable (hFR : IsFlat B (W ∪ R))
include hFR

lemma lemma6_le {Y : Finset α} (hY : IsFlat B Y) (hYP : ¬ Y ⊆ W ∪ P) (hYQ : ¬ Y ⊆ W ∪ Q) :
    (Y ∩ P).card ≤ (Y ∩ Q).card := by
  obtain ⟨x0, hx0Y, hx0R⟩ := lemma6_meets hB hWP hWQ hPQ hcover hFP hFQ hY hYP hYQ
  have hcoverPRQ : ∀ x, x ∈ W ∨ x ∈ P ∨ x ∈ R ∨ x ∈ Q := by
    intro x; rcases hcover x with h | h | h | h <;> simp [h]
  have key : ∀ y ∈ Y ∩ P, ∃ c, c ∈ Y ∩ Q ∧ ∃ A ∈ B, x0 ∈ A ∧ y ∈ A ∧ c ∈ A := by
    intro y hy
    obtain ⟨hyY, hyP⟩ := mem_inter.1 hy
    have hne : y ≠ x0 := fun h => Finset.disjoint_left.1 hPR hyP (h ▸ hx0R)
    obtain ⟨A, ⟨hA, hyA, hxA⟩, -⟩ := hB.2 y x0 hne
    obtain ⟨c, hcA, hcy, hcx⟩ := third_point A (hB.1 A hA) y x0 hne
    have hcQ := lemma6_third hB hWP hWR hPR hcoverPRQ hFP hFR hA hyA hyP hxA hx0R
      hcA hcy hcx
    have hAY := IsFlat.subset_of_two hB hY hA hne hyA hxA hyY hx0Y
    exact ⟨c, mem_inter.2 ⟨hAY hcA, hcQ⟩, A, hA, hxA, hyA, hcA⟩
  choose! f hf using key
  refine card_le_card_of_injOn f (fun y hy => (hf y hy).1) ?_
  intro y hy y' hy' hyy
  by_contra hne
  obtain ⟨hcYQ, A, hA, hxA, hyA, hcA⟩ := hf y hy
  obtain ⟨-, A', hA', hxA', hyA', hcA'⟩ := hf y' hy'
  rw [← hyy] at hcA'
  have hP := (mem_inter.1 (Finset.mem_coe.1 hy)).2
  have hP' := (mem_inter.1 (Finset.mem_coe.1 hy')).2
  have hcQ := (mem_inter.1 hcYQ).2
  have hxc : x0 ≠ f y := fun h => Finset.disjoint_left.1 hQR hcQ (h ▸ hx0R)
  have hAA : A = A' := by
    obtain ⟨A0, -, huniq⟩ := hB.2 x0 (f y) hxc
    rw [huniq A ⟨hA, hxA, hcA⟩, huniq A' ⟨hA', hxA', hcA'⟩]
  rw [← hAA] at hyA'
  refine card_four_le (hB.1 A hA) hxA hyA hyA' hcA ?_ ?_ hxc hne ?_ ?_
  · exact fun h => Finset.disjoint_left.1 hPR hP (h ▸ hx0R)
  · exact fun h => Finset.disjoint_left.1 hPR hP' (h ▸ hx0R)
  · exact fun h => Finset.disjoint_left.1 hPQ hP (h ▸ hcQ)
  · exact fun h => Finset.disjoint_left.1 hPQ hP' (h ▸ hcQ)

end Lemma6

/-- **Lemma 6.** Let `B` be an STS on `α` and `α = W ∪ Z₁ ∪ Z₂ ∪ Z₃` a partition such that
`W ∪ Z₁`, `W ∪ Z₂`, `W ∪ Z₃` are flats. If `Y` is a flat not contained in any `W ∪ Zᵢ`, then
`|Y ∩ Z₁| = |Y ∩ Z₂| = |Y ∩ Z₃|`. (The paper also assumes that `W` is a flat; this is not
needed.) -/
theorem lemma6 [Fintype α] (B : Finset (Finset α)) (hB : IsSTS B) (W Z₁ Z₂ Z₃ : Finset α)
    (hW1 : Disjoint W Z₁) (hW2 : Disjoint W Z₂) (hW3 : Disjoint W Z₃)
    (h12 : Disjoint Z₁ Z₂) (h13 : Disjoint Z₁ Z₃) (h23 : Disjoint Z₂ Z₃)
    (hcover : W ∪ Z₁ ∪ Z₂ ∪ Z₃ = Finset.univ)
    (hF1 : IsFlat B (W ∪ Z₁)) (hF2 : IsFlat B (W ∪ Z₂)) (hF3 : IsFlat B (W ∪ Z₃))
    (Y : Finset α) (hY : IsFlat B Y)
    (hY1 : ¬ Y ⊆ W ∪ Z₁) (hY2 : ¬ Y ⊆ W ∪ Z₂) (hY3 : ¬ Y ⊆ W ∪ Z₃) :
    (Y ∩ Z₁).card = (Y ∩ Z₂).card ∧ (Y ∩ Z₂).card = (Y ∩ Z₃).card := by
  have hc : ∀ x, x ∈ W ∨ x ∈ Z₁ ∨ x ∈ Z₂ ∨ x ∈ Z₃ := by
    intro x
    have : x ∈ W ∪ Z₁ ∪ Z₂ ∪ Z₃ := hcover ▸ mem_univ x
    simp only [mem_union] at this; tauto
  have hc213 : ∀ x, x ∈ W ∨ x ∈ Z₂ ∨ x ∈ Z₁ ∨ x ∈ Z₃ := fun x => by have := hc x; tauto
  have hc231 : ∀ x, x ∈ W ∨ x ∈ Z₂ ∨ x ∈ Z₃ ∨ x ∈ Z₁ := fun x => by have := hc x; tauto
  have hc321 : ∀ x, x ∈ W ∨ x ∈ Z₃ ∨ x ∈ Z₂ ∨ x ∈ Z₁ := fun x => by have := hc x; tauto
  have a := lemma6_le hB hW1 hW2 hW3 h12 h13 h23 hc hF1 hF2 hF3 hY hY1 hY2
  have b := lemma6_le hB hW2 hW1 hW3 h12.symm h23 h13 hc213 hF2 hF1 hF3 hY hY2 hY1
  have c := lemma6_le hB hW2 hW3 hW1 h23 h12.symm h13.symm hc231 hF2 hF3 hF1 hY hY2 hY3
  have d := lemma6_le hB hW3 hW2 hW1 h23.symm h13.symm h12.symm hc321 hF3 hF2 hF1 hY hY3 hY2
  omega

end STS
