/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.T4Setup

/-!
# Counting permutations permuting the sets `Rᵢ`
-/

@[expose] public section

open Finset

namespace STS.T4

variable {w m : ℕ}

/-- The parts `W, Z₀, Z₁, Z₂`. -/
def parts (w m : ℕ) : Option (Fin 3) → Finset (Pt w m)
  | none => Wset w m
  | some i => Zset w m i

/-- The parts permuted by `π`. -/
def partsπ (w m : ℕ) (π : Fin 3 → Fin 3) : Option (Fin 3) → Finset (Pt w m)
  | none => Wset w m
  | some i => Zset w m (π i)

lemma parts_cover (x : Pt w m) : ∃ o, x ∈ parts w m o := by
  rcases cover x with h | h | h | h
  · exact ⟨none, h⟩
  · exact ⟨some 0, h⟩
  · exact ⟨some 1, h⟩
  · exact ⟨some 2, h⟩

lemma Rset_ne (hm : 0 < m) {i j : Fin 3} (hij : i ≠ j) : Rset w m i ≠ Rset w m j := by
  intro h
  have h1 := Rset_inter (w := w) (m := m) hij
  rw [h, inter_self] at h1
  have := card_Rset (w := w) (m := m) j
  rw [h1, card_Wset] at this
  omega

lemma card_inj33 : ((univ : Finset (Fin 3 → Fin 3)).filter Function.Injective).card = 6 := by
  decide

lemma prod_parts (hw : w ≤ 1) :
    ∏ o, (parts w m o).card.factorial = m.factorial ^ 3 := by
  rw [Fintype.prod_option, Fin.prod_univ_three]
  simp only [parts, card_Wset, card_Zset]
  interval_cases w <;> simp [pow_succ]

/-- At most `3! (m!)³` permutations map each `Rᵢ` onto some `Rⱼ`. -/
theorem card_perm_R (hw : w ≤ 1) (hm : 0 < m) :
    (univ.filter (fun σ : Equiv.Perm (Pt w m) =>
      ∀ i, ∃ j, (Rset w m i).image σ = Rset w m j)).card ≤ 6 * m.factorial ^ 3 := by
  classical
  have hsub : univ.filter (fun σ : Equiv.Perm (Pt w m) =>
      ∀ i, ∃ j, (Rset w m i).image σ = Rset w m j) ⊆
      ((univ : Finset (Fin 3 → Fin 3)).filter Function.Injective).biUnion
        (fun π => univ.filter (fun σ : Equiv.Perm (Pt w m) =>
          ∀ o, (parts w m o).image σ = partsπ w m π o)) := by
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    choose π hπ using hσ
    have hinj : Function.Injective π := by
      intro i i' h
      by_contra hne
      apply Rset_ne (w := w) hm hne
      have := (hπ i).trans ((congrArg (Rset w m) h).trans (hπ i').symm)
      exact image_injective σ.injective this
    have hW : (Wset w m).image σ = Wset w m := by
      conv_lhs => rw [← Rset_inter (show (0 : Fin 3) ≠ 1 by decide)]
      rw [image_inter_of_injOn _ _ σ.injective.injOn, hπ, hπ, Rset_inter (hinj.ne (by decide))]
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    refine ⟨π, hinj, ?_⟩
    rintro (_ | i)
    · exact hW
    · simp only [parts, partsπ]
      rw [← Rset_sdiff, image_sdiff_of_injOn σ.injective.injOn
        (by rw [Rset_eq]; exact subset_union_left), hπ, hW, Rset_sdiff]
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  calc ∑ π ∈ (univ : Finset (Fin 3 → Fin 3)).filter Function.Injective,
        (univ.filter (fun σ : Equiv.Perm (Pt w m) =>
          ∀ o, (parts w m o).image σ = partsπ w m π o)).card
      ≤ ∑ _π ∈ (univ : Finset (Fin 3 → Fin 3)).filter Function.Injective, m.factorial ^ 3 := by
        refine sum_le_sum (fun π _ => ?_)
        rw [← prod_parts (m := m) hw]
        exact card_perm_maps_le _ _ parts_cover
    _ = 6 * m.factorial ^ 3 := by rw [sum_const, card_inj33, smul_eq_mul]

end STS.T4
