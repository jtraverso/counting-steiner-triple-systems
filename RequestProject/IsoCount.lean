/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Flats
public import RequestProject.Basic

/-!
# Counting isomorphism classes

* `STS.card_le_mul_N` : if `C` is a set of STS's on a `v`-set `X` and each system of `C` is
  mapped into `C` by at most `K` permutations of `X`, then `|C| ≤ K · N(v)`.
* `STS.card_perm_maps_le` : the number of permutations mapping each part of a partition onto a
  prescribed set is at most the product of the factorials of the part sizes.
* `STS.IsFlat.mapBlocks` : images of flats are flats.
-/

@[expose] public section

open Finset

namespace STS

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem card_le_mul_N {v : ℕ} (e : X ≃ Fin v) (C : Finset (Finset (Finset X)))
    (hC : ∀ c ∈ C, IsSTS c) (K : ℕ)
    (hK : ∀ c0 ∈ C, (univ.filter (fun σ : Equiv.Perm X => mapBlocks σ c0 ∈ C)).card ≤ K) :
    C.card ≤ K * N v := by
  classical
  haveI := Fintype.ofFinite (Quotient (isoSetoid v))
  let f : C → Quotient (isoSetoid v) := fun c =>
    Quotient.mk _ ⟨mapBlocks e c.1, isSTS_mapBlocks_equiv e (hC c.1 c.2)⟩
  have h1 : C.attach.card ≤ K * (C.attach.image f).card := by
    refine Finset.card_le_mul_card_image (f := f) _ K ?_
    intro q hq
    obtain ⟨c0, -, rfl⟩ := mem_image.1 hq
    have hsub : (C.attach.filter (fun x => f x = f c0)).map (Function.Embedding.subtype _) ⊆
        (univ.filter (fun σ : Equiv.Perm X => mapBlocks σ c0.1 ∈ C)).image
          (fun σ : Equiv.Perm X => mapBlocks (⇑σ) c0.1) := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := mem_map.1 hc
      have hfc := (mem_filter.1 hc').2
      obtain ⟨τ, hτ⟩ := Quotient.exact hfc.symm
      have hmap : mapBlocks (e.trans (τ.trans e.symm)) c0.1 = c'.1 := by
        have h := congrArg (mapBlocks e.symm) hτ
        simp only at h
        rw [mapBlocks_comp, mapBlocks_comp, mapBlocks_symm_mapBlocks] at h
        rw [← h]; rfl
      refine mem_image.2 ⟨e.trans (τ.trans e.symm), mem_filter.2 ⟨mem_univ _, ?_⟩, hmap⟩
      rw [hmap]; exact c'.2
    have := card_le_card hsub
    rw [card_map] at this
    exact this.trans (card_image_le.trans (hK c0.1 c0.2))
  have h2 : (C.attach.image f).card ≤ N v := by
    rw [N, Nat.card_eq_fintype_card]; exact card_le_univ _
  rw [card_attach] at h1
  exact h1.trans (Nat.mul_le_mul_left _ h2)

lemma card_stab_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Finset X)
    (hA : ∀ x, ∃ i, x ∈ A i) :
    (univ.filter (fun τ : Equiv.Perm X => ∀ i, (A i).image τ = A i)).card ≤
      ∏ i, (A i).card.factorial := by
  classical
  have hiff : ∀ τ : Equiv.Perm X, (∀ i, (A i).image τ = A i) → ∀ i x, x ∈ A i ↔ τ x ∈ A i := by
    intro τ hτ i x
    constructor
    · intro hx; rw [← hτ i]; exact mem_image_of_mem _ hx
    · intro hx; rw [← hτ i] at hx
      obtain ⟨y, hy, hyx⟩ := mem_image.1 hx
      rwa [← τ.injective hyx]
  let g : (univ.filter (fun τ : Equiv.Perm X => ∀ i, (A i).image τ = A i)) →
      (∀ i, Equiv.Perm (A i)) :=
    fun τ i => τ.1.subtypePerm (fun x => (hiff τ.1 (mem_filter.1 τ.2).2 i x).symm)
  have hg : Function.Injective g := by
    intro τ τ' h
    apply Subtype.ext; ext x
    obtain ⟨i, hi⟩ := hA x
    have := congrArg (fun f => (f i ⟨x, hi⟩ : X)) h
    simpa [g] using this
  have := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_coe, Fintype.card_pi, Fintype.card_perm] at this
  exact this

theorem card_perm_maps_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : ι → Finset X)
    (hA : ∀ x, ∃ i, x ∈ A i) :
    (univ.filter (fun σ : Equiv.Perm X => ∀ i, (A i).image σ = B i)).card ≤
      ∏ i, (A i).card.factorial := by
  classical
  rcases (univ.filter (fun σ : Equiv.Perm X => ∀ i, (A i).image σ = B i)).eq_empty_or_nonempty
    with h | ⟨σ0, hσ0⟩
  · rw [h]; exact Nat.zero_le _
  refine le_trans ?_ (card_stab_le A hA)
  refine card_le_card_of_injOn (fun σ => σ0⁻¹ * σ) ?_ ?_
  · intro σ hσ
    simp only [mem_filter, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hσ hσ0 ⊢
    intro i
    rw [Equiv.Perm.coe_mul, ← Finset.image_image, hσ i, ← hσ0 i, Finset.image_image]
    simp
  · intro σ _ σ' _ h
    simpa using h

omit [Fintype X] in
/-- Images of flats under a bijection are flats. -/
lemma IsFlat.mapBlocks_equiv {Y : Type*} [DecidableEq Y] (σ : X ≃ Y) {B : Finset (Finset X)}
    {F : Finset X} (hF : IsFlat B F) : IsFlat (mapBlocks σ B) (F.image σ) := by
  intro A hA
  obtain ⟨A0, hA0, rfl⟩ := mem_image.1 hA
  rw [← image_inter_of_injOn _ _ σ.injective.injOn, card_image_of_injective _ σ.injective]
  exact hF A0 hA0

end STS
