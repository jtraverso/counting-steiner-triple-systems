/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Random orderings and box counting

Linial and Luria reveal the entries of a Steiner triple system (or of a 1-factorization)
in a random order: first a random order `≪` of the vertices, then, for every vertex `u`, a
random order of the edges `{u, w}` with `u ≪ w`.

We realise these random orders by random *labels*: a pair `(λ, ν)` of maps
`Fin n → Fin L`, chosen uniformly.  The vertices are ordered by the rank
`vpos λ v = λ v * n + v` (labels, ties broken by the index), and the edges `{u, w}` of the
star of `u` are ordered by the rank `vpos ν w` of their other endpoint.  The order in which
the (ordered) pairs `(a, b)`, `a ≠ b`, are revealed is given by the injective key `ekey λ ν`.

All probabilities are then counts of "boxes" `{ν | ∀ v ∈ D, ν v ∈ A v}`; see `card_boxF`.
-/

@[expose] public section

open Finset

namespace LinialLuria

variable {n L : ℕ}

/-- The rank of the vertex `v` in the order defined by the labels `lam`. -/
def vpos (lam : Fin n → Fin L) (v : Fin n) : ℕ := (lam v : ℕ) * n + v

lemma vpos_lt (lam : Fin n → Fin L) (v : Fin n) : vpos lam v < L * n := by
  unfold vpos
  have h1 := (lam v).isLt
  have h2 := v.isLt
  nlinarith

lemma vpos_inj (lam : Fin n → Fin L) {v w : Fin n} (h : vpos lam v = vpos lam w) : v = w := by
  unfold vpos at h
  have h1 := v.isLt
  have h2 := w.isLt
  have := congrArg (· % n) h
  simp only [Nat.mul_add_mod_of_lt h1, Nat.mul_add_mod_of_lt h2] at this
  exact Fin.ext this

lemma vpos_ne (lam : Fin n → Fin L) {v w : Fin n} (h : v ≠ w) : vpos lam v ≠ vpos lam w :=
  fun e => h (vpos_inj lam e)

/-- The key of the ordered pair `p = (a, b)`: if `a ≪ b` the pair is the edge `{a, b}` of the
star of `a`; otherwise it is revealed right after the pair `(b, a)`. -/
def ekey (lam nu : Fin n → Fin L) (p : Fin n × Fin n) : ℕ :=
  if vpos lam p.1 < vpos lam p.2 then (vpos lam p.1 * (L * n) + vpos nu p.2) * 2
  else (vpos lam p.2 * (L * n) + vpos nu p.1) * 2 + 1

lemma div_mod_key {A B M : ℕ} (hB : B < M) : (A * M + B) / M = A ∧ (A * M + B) % M = B := by
  have hM : 0 < M := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hB, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hB]

lemma ekey_injOn (lam nu : Fin n → Fin L) :
    Set.InjOn (ekey lam nu) (offDiag (univ : Finset (Fin n))) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
  simp only [coe_offDiag, coe_univ, Set.mem_univ, true_and, Set.mem_offDiag] at hab hcd
  have hb := vpos_lt nu b
  have ha := vpos_lt nu a
  have hc := vpos_lt nu c
  have hd := vpos_lt nu d
  unfold ekey at h
  simp only at h
  split_ifs at h with h1 h2 h2
  · have h' : vpos lam a * (L * n) + vpos nu b = vpos lam c * (L * n) + vpos nu d := by omega
    have e1 := div_mod_key (A := vpos lam a) hb
    have e2 := div_mod_key (A := vpos lam c) hd
    rw [h'] at e1
    have : a = c := vpos_inj lam (e1.1.symm.trans e2.1)
    have : b = d := vpos_inj nu (e1.2.symm.trans e2.2)
    simp_all
  · omega
  · omega
  · have h' : vpos lam b * (L * n) + vpos nu a = vpos lam d * (L * n) + vpos nu c := by omega
    have e1 := div_mod_key (A := vpos lam b) ha
    have e2 := div_mod_key (A := vpos lam d) hc
    rw [h'] at e1
    have : b = d := vpos_inj lam (e1.1.symm.trans e2.1)
    have : a = c := vpos_inj nu (e1.2.symm.trans e2.2)
    simp_all

lemma ekey_le_of_first (lam nu : Fin n → Fin L) (a b : Fin n) (F : ℕ)
    (hF : vpos lam a ≤ F ∨ vpos lam b ≤ F) :
    ekey lam nu (a, b) < (F + 1) * (L * n) * 2 := by
  have hb := vpos_lt nu b
  have ha := vpos_lt nu a
  unfold ekey
  simp only
  split_ifs with h
  · have : vpos lam a ≤ F := by omega
    nlinarith
  · have : vpos lam b ≤ F := by omega
    nlinarith

lemma ekey_ge_of_first (lam nu : Fin n → Fin L) (i j : Fin n) (h : vpos lam i < vpos lam j) :
    vpos lam i * (L * n) * 2 ≤ ekey lam nu (i, j) := by
  unfold ekey
  simp only [if_pos h]
  nlinarith

/-- A pair one of whose vertices precedes `i` is revealed before every pair `(i, j)` with
`i ≪ j`. -/
lemma ekey_lt_of_before (lam nu : Fin n → Fin L) (a b i j : Fin n)
    (hab : vpos lam a < vpos lam i ∨ vpos lam b < vpos lam i) (hij : vpos lam i < vpos lam j) :
    ekey lam nu (a, b) < ekey lam nu (i, j) := by
  have hpos : 0 < vpos lam i := by omega
  have h1 := ekey_le_of_first lam nu a b (vpos lam i - 1) (by omega)
  have h2 := ekey_ge_of_first lam nu i j hij
  have : vpos lam i - 1 + 1 = vpos lam i := by omega
  rw [this] at h1
  omega

/-- Within the star of `i`, the pair `(i, t)` is revealed before `(i, j)` if `t` comes
before `j` in the edge order. -/
lemma ekey_lt_star (lam nu : Fin n → Fin L) (i j t : Fin n) (hij : vpos lam i < vpos lam j)
    (hit : vpos lam i < vpos lam t) (htj : vpos nu t < vpos nu j) :
    ekey lam nu (i, t) < ekey lam nu (i, j) := by
  unfold ekey
  simp only [if_pos hij, if_pos hit]
  omega

/-- If `j ≪ i` then `(j, i)` is revealed before `(i, j)`. -/
lemma ekey_lt_swap (lam nu : Fin n → Fin L) (i j : Fin n) (hji : vpos lam j < vpos lam i) :
    ekey lam nu (j, i) < ekey lam nu (i, j) := by
  unfold ekey
  simp only [if_pos hji, if_neg (show ¬ vpos lam i < vpos lam j by omega)]
  omega

/-! ### Boxes -/

/-- The labels `y` of a vertex `v` such that `v` comes after a vertex `j` of label `z`. -/
def afterSet (z : Fin L) (j v : Fin n) : Finset (Fin L) :=
  univ.filter (fun y : Fin L => (z : ℕ) * n + j < (y : ℕ) * n + v)

lemma mem_afterSet_iff (lam : Fin n → Fin L) (j v : Fin n) :
    lam v ∈ afterSet (lam j) j v ↔ vpos lam j < vpos lam v := by
  simp [afterSet, vpos]

lemma card_afterSet_le (z : Fin L) (j v : Fin n) : (afterSet z j v).card ≤ L - z := by
  have hsub : afterSet z j v ⊆ univ.filter (fun y : Fin L => z ≤ y) := by
    intro y hy
    simp only [afterSet, mem_filter, mem_univ, true_and] at hy ⊢
    by_contra h
    push_neg at h
    have h1 : (y : ℕ) + 1 ≤ z := h
    have h2 := v.isLt
    nlinarith
  refine (card_le_card hsub).trans (le_of_eq ?_)
  have : univ.filter (fun y : Fin L => z ≤ y) = Finset.Ici z := by ext; simp
  rw [this, Fin.card_Ici]

/-- The box `{ν | ∀ v ∈ D, ν v ∈ A v}`. -/
def boxF {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β] (D : Finset V)
    (A : V → Finset β) : Finset (V → β) :=
  univ.filter (fun nu => ∀ v ∈ D, nu v ∈ A v)

lemma card_boxF {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
    (D : Finset V) (A : V → Finset β) :
    (boxF D A).card * (Fintype.card β) ^ D.card =
      (Fintype.card β) ^ (Fintype.card V) * ∏ v ∈ D, (A v).card := by
  classical
  have h : boxF D A = Fintype.piFinset (fun v => if v ∈ D then A v else univ) := by
    ext nu
    simp only [boxF, mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h v
      split_ifs with hv
      · exact h v hv
      · exact mem_univ _
    · intro h v hv
      have := h v
      rwa [if_pos hv] at this
  rw [h, Fintype.card_piFinset]
  rw [← prod_mul_prod_compl D]
  have h1 : ∏ v ∈ D, (if v ∈ D then A v else univ).card = ∏ v ∈ D, (A v).card :=
    prod_congr rfl (fun v hv => by rw [if_pos hv])
  have h2 : ∏ v ∈ Dᶜ, (if v ∈ D then A v else (univ : Finset β)).card =
      (Fintype.card β) ^ Dᶜ.card := by
    rw [prod_congr rfl (fun v hv => by rw [if_neg (mem_compl.1 hv)]), prod_const, card_univ]
  rw [h1, h2, card_compl]
  have hle : D.card ≤ Fintype.card V := card_le_univ D
  calc (∏ v ∈ D, (A v).card) * Fintype.card β ^ (Fintype.card V - D.card) *
        Fintype.card β ^ D.card
      = (∏ v ∈ D, (A v).card) * Fintype.card β ^ (Fintype.card V - D.card + D.card) := by
        rw [pow_add]; ring
    _ = _ := by rw [Nat.sub_add_cancel hle]; ring

lemma boxF_card_le {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
    (D : Finset V) (A : V → Finset β) (q : V → ℕ) (hq : ∀ v ∈ D, (A v).card ≤ q v) :
    (boxF D A).card * (Fintype.card β) ^ D.card ≤
      (Fintype.card β) ^ (Fintype.card V) * ∏ v ∈ D, q v := by
  rw [card_boxF]
  exact Nat.mul_le_mul_left _ (prod_le_prod' hq)

lemma boxF_ratio {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
    (D E : Finset V) (hDE : Disjoint D E) (A : V → Finset β) (q : ℕ)
    (hq : ∀ v ∈ E, (A v).card ≤ q) :
    (boxF (D ∪ E) A).card * (Fintype.card β) ^ E.card ≤ (boxF D A).card * q ^ E.card := by
  have hβ : 0 < Fintype.card β ∨ Fintype.card β = 0 := by omega
  rcases hβ with hβ | hβ
  · have h1 := card_boxF (D ∪ E) A
    have h2 := card_boxF D A
    rw [card_union_of_disjoint hDE, prod_union hDE, pow_add] at h1
    have hE : ∏ v ∈ E, (A v).card ≤ q ^ E.card := by
      rw [← prod_const]; exact prod_le_prod' hq
    have hpos : 0 < Fintype.card β ^ D.card := pow_pos hβ _
    apply le_of_mul_le_mul_right _ hpos
    calc (boxF (D ∪ E) A).card * Fintype.card β ^ E.card * Fintype.card β ^ D.card
        = (boxF (D ∪ E) A).card * (Fintype.card β ^ D.card * Fintype.card β ^ E.card) := by ring
      _ = Fintype.card β ^ Fintype.card V * ((∏ v ∈ D, (A v).card) * ∏ v ∈ E, (A v).card) := h1
      _ ≤ Fintype.card β ^ Fintype.card V * ((∏ v ∈ D, (A v).card) * q ^ E.card) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hE)
      _ = (boxF D A).card * Fintype.card β ^ D.card * q ^ E.card := by rw [h2]; ring
      _ = _ := by ring
  · -- `β` empty: every box over a nonempty `V` is empty
    by_cases hV : IsEmpty V
    · have : ∀ F : Finset V, F = ∅ := fun F => Finset.eq_empty_of_isEmpty F
      rw [this E]
      simp
    · rw [not_isEmpty_iff] at hV
      obtain ⟨v⟩ := hV
      have : IsEmpty (V → β) := by
        rw [Fintype.card_eq_zero_iff] at hβ
        exact ⟨fun f => hβ.false (f v)⟩
      simp [Finset.eq_empty_of_isEmpty (boxF (D ∪ E) A)]

/-- Summing over all label maps `ν` by the value `ν j`. -/
lemma sum_split_value {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]
    (j : V) (g : (V → β) → ℝ) :
    ∑ nu, g nu = ∑ z : β, ∑ nu ∈ univ.filter (fun nu : V → β => nu j = z), g nu := by
  rw [sum_fiberwise]

/-- Reindexing `z ↦ L - z`. -/
lemma sum_fin_reflect (L : ℕ) (g : ℝ → ℝ) :
    ∑ z : Fin L, g ((L : ℝ) - (z : ℕ)) = ∑ r ∈ range L, g ((r : ℝ) + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun z => g ((L : ℝ) - z)) L]
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro r hr
  have hr' := mem_range.1 hr
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

end LinialLuria
