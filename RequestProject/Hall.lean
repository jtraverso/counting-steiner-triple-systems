/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Defs

/-!
# M. Hall Jr.'s theorem on the number of systems of distinct representatives

If a family of `n` finite sets satisfies Hall's condition and every set has at least `r ≤ n`
elements, then it has at least `r!` systems of distinct representatives.
-/

@[expose] public section

open Finset

namespace STS
namespace Hall

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

open Classical in
/-- Partial systems of distinct representatives of `A` on the index set `s`, encoded as
`Option`-valued functions which are `none` off `s`. -/
noncomputable def sdr (A : ι → Finset α) (s : Finset ι) : Finset (ι → Option α) :=
  univ.filter (fun f => (∀ i, i ∉ s → f i = none) ∧ (∀ i ∈ s, ∃ a ∈ A i, f i = some a) ∧
    ∀ i ∈ s, ∀ j ∈ s, f i = f j → i = j)

lemma mem_sdr {A : ι → Finset α} {s : Finset ι} {f : ι → Option α} :
    f ∈ sdr A s ↔ (∀ i, i ∉ s → f i = none) ∧ (∀ i ∈ s, ∃ a ∈ A i, f i = some a) ∧
      ∀ i ∈ s, ∀ j ∈ s, f i = f j → i = j := by
  unfold sdr; simp

/-- Hall's condition for the family `A` restricted to `s`. -/
def HallOn (A : ι → Finset α) (s : Finset ι) : Prop :=
  ∀ t ⊆ s, t.card ≤ (t.biUnion A).card

lemma count_aux (n : ℕ) : ∀ (s : Finset ι) (A : ι → Finset α) (r : ℕ), s.card = n →
    HallOn A s → (∀ i ∈ s, r ≤ (A i).card) → r ≤ s.card → r.factorial ≤ (sdr A s).card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s A r hn hHall hA hr
  rcases s.eq_empty_or_nonempty with hs | hs
  · -- empty index set
    subst hs
    simp only [card_empty, nonpos_iff_eq_zero] at hr
    subst hr
    rw [Nat.factorial_zero, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, card_pos]
    exact ⟨fun _ => none, mem_sdr.2 ⟨fun _ _ => rfl, by simp, by simp⟩⟩
  by_cases hcrit : ∃ t ⊆ s, t.Nonempty ∧ t ≠ s ∧ (t.biUnion A).card ≤ t.card
  · -- a critical proper subfamily
    obtain ⟨t, hts, htne, hts', htcrit⟩ := hcrit
    have htlt : t.card < s.card := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hts, hts'⟩)
    obtain ⟨i₁, hi₁⟩ := htne
    have hrt : r ≤ t.card :=
      (hA i₁ (hts hi₁)).trans ((card_le_card (subset_biUnion_of_mem A hi₁)).trans htcrit)
    have h1 := ih t.card (hn ▸ htlt) t A r rfl (fun u hu => hHall u (hu.trans hts))
      (fun i hi => hA i (hts hi)) hrt
    set U := t.biUnion A with hU
    set A'' : ι → Finset α := fun i => A i \ U
    have hHall'' : HallOn A'' (s \ t) := by
      intro u hu
      have hdisj : Disjoint u t := by
        rw [Finset.disjoint_left]; intro i hiu hit; exact (mem_sdiff.1 (hu hiu)).2 hit
      have h1 := hHall (u ∪ t) (union_subset (hu.trans sdiff_subset) hts)
      rw [card_union_of_disjoint hdisj, Finset.union_biUnion, ← hU] at h1
      have h2 : u.biUnion A ∪ U ⊆ u.biUnion A'' ∪ U := by
        intro a ha
        rw [mem_union] at ha ⊢
        by_cases haU : a ∈ U
        · exact Or.inr haU
        · rcases ha with ha | ha
          · left
            obtain ⟨i, hi, hai⟩ := mem_biUnion.1 ha
            exact mem_biUnion.2 ⟨i, hi, mem_sdiff.2 ⟨hai, haU⟩⟩
          · exact absurd ha haU
      have h3 := (card_le_card h2).trans (card_union_le _ _)
      omega
    have hlt2 : (s \ t).card < n := by
      rw [card_sdiff_of_subset hts]; obtain ⟨i, hi⟩ := hs; have := card_pos.2 ⟨i₁, hi₁⟩; omega
    have h2 := ih (s \ t).card hlt2 (s \ t) A'' 0 rfl hHall'' (fun _ _ => Nat.zero_le _)
      (Nat.zero_le _)
    rw [Nat.factorial_zero, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, card_pos] at h2
    obtain ⟨h, hh⟩ := h2
    rw [mem_sdr] at hh
    refine h1.trans (card_le_card_of_injOn (fun g i => if i ∈ t then g i else h i) ?_ ?_)
    · intro g hg
      rw [mem_coe, mem_sdr] at hg
      rw [mem_coe, mem_sdr]
      refine ⟨?_, ?_, ?_⟩
      · intro i his
        have hit : i ∉ t := fun h' => his (hts h')
        simp only [hit, if_false]
        exact hh.1 i (fun h' => his (mem_sdiff.1 h').1)
      · intro i his
        by_cases hit : i ∈ t
        · simp only [hit, if_true]; exact hg.2.1 i hit
        · simp only [hit, if_false]
          obtain ⟨a, ha, he⟩ := hh.2.1 i (mem_sdiff.2 ⟨his, hit⟩)
          exact ⟨a, (mem_sdiff.1 ha).1, he⟩
      · intro i his j hjs hij
        by_cases hit : i ∈ t <;> by_cases hjt : j ∈ t <;> simp only [hit, hjt, if_true,
          if_false] at hij
        · exact hg.2.2 i hit j hjt hij
        · exfalso
          obtain ⟨a, ha, hea⟩ := hg.2.1 i hit
          obtain ⟨b, hb, heb⟩ := hh.2.1 j (mem_sdiff.2 ⟨hjs, hjt⟩)
          rw [hea, heb, Option.some_inj] at hij
          subst hij
          exact (mem_sdiff.1 hb).2 (mem_biUnion.2 ⟨i, hit, ha⟩)
        · exfalso
          obtain ⟨a, ha, hea⟩ := hg.2.1 j hjt
          obtain ⟨b, hb, heb⟩ := hh.2.1 i (mem_sdiff.2 ⟨his, hit⟩)
          rw [hea, heb, Option.some_inj] at hij
          subst hij
          exact (mem_sdiff.1 hb).2 (mem_biUnion.2 ⟨j, hjt, ha⟩)
        · exact hh.2.2 i (mem_sdiff.2 ⟨his, hit⟩) j (mem_sdiff.2 ⟨hjs, hjt⟩) hij
    · intro g hg g' hg' heq
      rw [mem_coe, mem_sdr] at hg hg'
      funext i
      have := congrFun heq i
      by_cases hit : i ∈ t
      · simpa [hit] using this
      · rw [hg.1 i hit, hg'.1 i hit]
  · -- no critical proper subfamily
    push_neg at hcrit
    obtain ⟨i₀, hi₀⟩ := hs
    have hA0 : 1 ≤ (A i₀).card := by
      have := hHall {i₀} (singleton_subset_iff.2 hi₀)
      simpa using this
    set s₀ := s.erase i₀
    have hs₀ : s₀.card = s.card - 1 := card_erase_of_mem hi₀
    have hpos : 0 < s.card := card_pos.2 ⟨i₀, hi₀⟩
    have key : ∀ x ∈ A i₀, (r - 1).factorial ≤ (sdr (fun i => (A i).erase x) s₀).card := by
      intro x _
      refine ih s₀.card (by omega) s₀ _ (r - 1) rfl ?_ ?_ (by omega)
      · intro u hu
        rcases u.eq_empty_or_nonempty with hu0 | hune
        · simp [hu0]
        have hus : u ⊆ s := hu.trans (erase_subset _ _)
        have hne : u ≠ s := by
          intro h; have : i₀ ∈ u := h ▸ hi₀; exact (notMem_erase i₀ s) (hu this)
        have h1 := hcrit u hus hune hne
        have h2 : (u.biUnion A).erase x ⊆ u.biUnion (fun i => (A i).erase x) := by
          intro a ha
          obtain ⟨hax, ha⟩ := mem_erase.1 ha
          obtain ⟨i, hi, hai⟩ := mem_biUnion.1 ha
          exact mem_biUnion.2 ⟨i, hi, mem_erase.2 ⟨hax, hai⟩⟩
        have h3 := card_le_card h2
        have h4 := pred_card_le_card_erase (s := u.biUnion A) (a := x)
        omega
      · intro i hi
        have := hA i (mem_of_mem_erase hi)
        have := pred_card_le_card_erase (s := A i) (a := x)
        omega
    -- combine
    let F : (Σ _ : α, ι → Option α) → (ι → Option α) := fun p => Function.update p.2 i₀ (some p.1)
    have hsub : ((A i₀).sigma (fun x => sdr (fun i => (A i).erase x) s₀)).card ≤
        (sdr A s).card := by
      refine card_le_card_of_injOn F ?_ ?_
      · rintro ⟨x, g⟩ hp
        rw [mem_coe, mem_sigma] at hp
        obtain ⟨hx, hg⟩ := hp
        dsimp only at hx hg
        rw [mem_sdr] at hg
        rw [mem_coe, mem_sdr]
        refine ⟨?_, ?_, ?_⟩
        · intro i his
          have hne : i ≠ i₀ := fun h => his (h ▸ hi₀)
          simp only [F, Function.update_of_ne hne]
          exact hg.1 i (fun h => his (mem_of_mem_erase h))
        · intro i his
          by_cases hii : i = i₀
          · subst hii; exact ⟨x, hx, by simp [F]⟩
          · simp only [F, Function.update_of_ne hii]
            obtain ⟨a, ha, he⟩ := hg.2.1 i (mem_erase.2 ⟨hii, his⟩)
            exact ⟨a, mem_of_mem_erase ha, he⟩
        · intro i his j hjs hij
          by_cases hii : i = i₀ <;> by_cases hjj : j = i₀
          · rw [hii, hjj]
          · exfalso
            subst hii
            simp only [F, Function.update_self, Function.update_of_ne hjj] at hij
            obtain ⟨a, ha, he⟩ := hg.2.1 j (mem_erase.2 ⟨hjj, hjs⟩)
            rw [he, Option.some_inj] at hij
            subst hij
            exact (mem_erase.1 ha).1 rfl
          · exfalso
            subst hjj
            simp only [F, Function.update_self, Function.update_of_ne hii] at hij
            obtain ⟨a, ha, he⟩ := hg.2.1 i (mem_erase.2 ⟨hii, his⟩)
            rw [he, Option.some_inj] at hij
            subst hij
            exact (mem_erase.1 ha).1 rfl
          · simp only [F, Function.update_of_ne hii, Function.update_of_ne hjj] at hij
            exact hg.2.2 i (mem_erase.2 ⟨hii, his⟩) j (mem_erase.2 ⟨hjj, hjs⟩) hij
      · rintro ⟨x, g⟩ hp ⟨x', g'⟩ hp' heq
        rw [mem_coe, mem_sigma, mem_sdr] at hp hp'
        dsimp only at hp hp'
        simp only [F] at heq
        have hx : x = x' := by
          have := congrFun heq i₀
          simpa using this
        subst hx
        have : g = g' := by
          funext i
          by_cases hii : i = i₀
          · subst hii
            rw [hp.2.1 i (notMem_erase i s), hp'.2.1 i (notMem_erase i s)]
          · have := congrFun heq i
            simpa [Function.update_of_ne hii] using this
        rw [this]
    rw [card_sigma] at hsub
    refine le_trans ?_ hsub
    calc r.factorial ≤ (A i₀).card * (r - 1).factorial := by
          rcases Nat.eq_zero_or_pos r with h0 | h0
          · subst h0; simpa using hA0
          · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
            simp only [Nat.add_sub_cancel, Nat.factorial_succ]
            exact Nat.mul_le_mul_right _ (hA i₀ hi₀)
      _ = ∑ _x ∈ A i₀, (r - 1).factorial := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := sum_le_sum key

end Hall

/-- **M. Hall Jr.'s theorem.** If a family of `n` finite sets `A i` (subsets of a finite type)
satisfies Hall's condition and every set has at least `r` elements, where `r ≤ n`, then the
family has at least `r!` systems of distinct representatives (injective choice functions). -/
theorem hall_sdr_count {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (A : ι → Finset α) (r : ℕ) (hr : r ≤ Fintype.card ι)
    (hHall : ∀ s : Finset ι, s.card ≤ (s.biUnion A).card) (hA : ∀ i, r ≤ (A i).card) :
    r.factorial ≤ Nat.card {f : ι → α // Function.Injective f ∧ ∀ i, f i ∈ A i} := by
  classical
  have h := Hall.count_aux _ univ A r rfl (fun t _ => hHall t) (fun i _ => hA i)
    (by rw [card_univ]; exact hr)
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : r = 0 := by rw [Fintype.card_eq_zero] at hr; omega
    subst this
    rw [Nat.factorial_zero, Nat.one_le_iff_ne_zero, Nat.card_ne_zero]
    exact ⟨⟨⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩⟩,
      inferInstance⟩
  obtain ⟨i₀⟩ := hι
  have hα : Nonempty α := by
    have := hHall {i₀}
    simp only [card_singleton, singleton_biUnion, Nat.one_le_iff_ne_zero, ne_eq, card_eq_zero] at this
    obtain ⟨a, _⟩ := Finset.nonempty_iff_ne_empty.2 this
    exact ⟨a⟩
  obtain ⟨a₀⟩ := hα
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine h.trans (card_le_card_of_injOn (fun g i => (g i).getD a₀) ?_ ?_)
  · intro g hg
    rw [mem_coe, Hall.mem_sdr] at hg
    rw [mem_coe, mem_filter]
    refine ⟨mem_univ _, ?_, ?_⟩
    · intro i j hij
      obtain ⟨a, ha, hea⟩ := hg.2.1 i (mem_univ _)
      obtain ⟨b, hb, heb⟩ := hg.2.1 j (mem_univ _)
      simp only [hea, heb, Option.getD_some] at hij
      subst hij
      exact hg.2.2 i (mem_univ _) j (mem_univ _) (hea.trans heb.symm)
    · intro i
      obtain ⟨a, ha, hea⟩ := hg.2.1 i (mem_univ _)
      simp [hea, ha]
  · intro g hg g' hg' heq
    rw [mem_coe, Hall.mem_sdr] at hg hg'
    funext i
    have := congrFun heq i
    obtain ⟨a, ha, hea⟩ := hg.2.1 i (mem_univ _)
    obtain ⟨b, hb, heb⟩ := hg'.2.1 i (mem_univ _)
    simp only [hea, heb, Option.getD_some] at this
    rw [hea, heb, this]

end STS
