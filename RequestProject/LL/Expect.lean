/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LL.Order
public import RequestProject.LL.Analysis

/-!
# Generic tools for the expectation estimates

* `Abox z j` : the box of label maps `ν` with `ν j = z` and (on the other coordinates of the
  box) `v` after `j`.
* `box_jensen` : Jensen's inequality on a box, in the form used twice in the paper
  (once for the vertex order and once for the edge order).
-/

@[expose] public section

open Finset

namespace LinialLuria

variable {n L : ℕ}

/-- The coordinate sets of the box "`ν j = z` and `j ≪ v` for the other coordinates". -/
def Abox (z : Fin L) (j : Fin n) : Fin n → Finset (Fin L) :=
  fun v => if v = j then {z} else afterSet z j v

lemma mem_boxF_Abox (z : Fin L) (j : Fin n) (D : Finset (Fin n)) (hjD : j ∉ D)
    (nu : Fin n → Fin L) :
    nu ∈ boxF (insert j D) (Abox z j) ↔ nu j = z ∧ ∀ v ∈ D, vpos nu j < vpos nu v := by
  simp only [boxF, mem_filter, mem_univ, true_and, forall_mem_insert, Abox, if_true,
    mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v hv => ?_⟩
    have hvj : v ≠ j := fun h => hjD (h ▸ hv)
    have := h2 v hv
    rw [if_neg hvj, ← h1] at this
    exact (mem_afterSet_iff nu j v).1 this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v hv => ?_⟩
    have hvj : v ≠ j := fun h => hjD (h ▸ hv)
    rw [if_neg hvj, ← h1]
    exact (mem_afterSet_iff nu j v).2 (h2 v hv)

lemma card_Abox_le (z : Fin L) (j v : Fin n) :
    (Abox z j v).card ≤ if v = j then 1 else L - z := by
  unfold Abox
  split_ifs
  · simp
  · exact card_afterSet_le z j v

lemma card_Abox_le' (z : Fin L) (j v : Fin n) (hv : v ≠ j) : (Abox z j v).card ≤ L - z := by
  have := card_Abox_le z j v
  rwa [if_neg hv] at this

lemma cast_sub_fin (z : Fin L) : ((L - z : ℕ) : ℝ) = (L : ℝ) - z := by
  rw [Nat.cast_sub z.isLt.le]

/-- Jensen's inequality on a finite set of label maps. -/
lemma box_jensen {γ : Type*} (B : Finset γ) (f : γ → ℕ) (β μ bound : ℝ) (hβ : 0 ≤ β)
    (hμ0 : 0 ≤ μ) (hμ : (∑ x ∈ B, (f x : ℝ)) ≤ μ * B.card) (hB : (B.card : ℝ) ≤ bound) :
    ∑ x ∈ B, Real.log (1 + β * f x) ≤ bound * Real.log (1 + β * μ) := by
  have hlog0 : 0 ≤ Real.log (1 + β * μ) := Real.log_nonneg (by nlinarith)
  rcases B.eq_empty_or_nonempty with rfl | hne
  · simp only [sum_empty, card_empty, Nat.cast_zero] at hB ⊢
    exact mul_nonneg hB hlog0
  have hc : (0 : ℝ) < B.card := by exact_mod_cast hne.card_pos
  have hJ := log_jensen B (fun x => β * f x) (fun x _ => by positivity)
  refine hJ.trans ?_
  rw [← mul_sum]
  have h1 : β * (∑ x ∈ B, (f x : ℝ)) / B.card ≤ β * μ := by
    rw [div_le_iff₀ hc]; nlinarith
  have h2 : Real.log (1 + β * (∑ x ∈ B, (f x : ℝ)) / B.card) ≤ Real.log (1 + β * μ) := by
    apply Real.log_le_log (by positivity)
    have : β * (∑ x ∈ B, (f x : ℝ)) / B.card = β * (∑ x ∈ B, (f x : ℝ)) / B.card := rfl
    linarith
  have h3 : (B.card : ℝ) * Real.log (1 + β * (∑ x ∈ B, (f x : ℝ)) / B.card) ≤
      B.card * Real.log (1 + β * μ) := mul_le_mul_of_nonneg_left h2 hc.le
  calc _ = (B.card : ℝ) * Real.log (1 + β * (∑ x ∈ B, (f x : ℝ)) / B.card) := by ring_nf
    _ ≤ B.card * Real.log (1 + β * μ) := h3
    _ ≤ bound * Real.log (1 + β * μ) := mul_le_mul_of_nonneg_right hB hlog0

/-- Counting a sum of cardinalities of filters. -/
lemma sum_card_filter_swap {γ δ : Type*} (B : Finset γ) (M : Finset δ) (P : γ → δ → Prop)
    [∀ x t, Decidable (P x t)] :
    ∑ x ∈ B, ((M.filter (fun t => P x t)).card : ℝ) =
      ∑ t ∈ M, ((B.filter (fun x => P x t)).card : ℝ) := by
  simp only [card_filter, Nat.cast_sum]
  rw [sum_comm]

end LinialLuria
