/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# A counting form of the entropy chain rule

Linial and Luria bound the entropy `H(X) = log |F|` of a uniformly random element `X` of a
finite set `F` by revealing `X` coordinate by coordinate, using the chain rule
`H(X) = ∑ H(X_s | X_t, t ≺ s)` and the bound `H(X_s | …) ≤ E[log N_s]`, where `N_s` bounds
the number of values still possible for `X_s`.

Here we prove the purely combinatorial statement that this argument yields (no probability
theory is needed): if the coordinates `f s`, `s ∈ I`, determine the elements of `S`, and the
coordinates are revealed in the order given by an injective `key : ι → ℕ`, then

`|S| log |S| ≤ ∑_{x ∈ S} ∑_{s ∈ I} log b_s(x)`,

where `b_s(x)` is the number of values of the coordinate `s` among the elements of `S` that
agree with `x` on all coordinates revealed before `s`.
-/

@[expose] public section

open Finset Real

namespace LinialLuria

/-- The log-sum inequality in the form used by the chain rule. -/
lemma log_sum_ineq {β : Type*} (P : Finset β) (s : β → ℕ) :
    ((∑ v ∈ P, s v : ℕ) : ℝ) * Real.log ((∑ v ∈ P, s v : ℕ) : ℝ) ≤
      ∑ v ∈ P, (s v : ℝ) * Real.log (s v) +
        ((∑ v ∈ P, s v : ℕ) : ℝ) * Real.log P.card := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simp
  have hd : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hJ := Real.convexOn_mul_log.map_sum_le (t := P) (w := fun _ => (1 : ℝ) / P.card)
    (p := fun v => (s v : ℝ)) (by intros; positivity)
    (by rw [sum_const, nsmul_eq_mul]; field_simp) (by intros; simp)
  simp only [smul_eq_mul] at hJ
  rw [← mul_sum, ← mul_sum] at hJ
  set S : ℝ := ∑ v ∈ P, (s v : ℝ) with hS
  push_cast
  rw [← hS]
  have key : 1 / (P.card : ℝ) * S * Real.log (1 / P.card * S) =
      1 / (P.card : ℝ) * (S * Real.log S - S * Real.log P.card) := by
    rcases eq_or_ne S 0 with h0 | h0
    · simp [h0]
    · rw [show 1 / (P.card : ℝ) * S = S / P.card by ring, Real.log_div h0 hd.ne']
      ring
  rw [key] at hJ
  have := (mul_le_mul_iff_of_pos_left (show (0:ℝ) < 1 / P.card by positivity)).1 hJ
  linarith

/-- The elements of `S` that agree with `x` on all coordinates revealed before `s`. -/
def agreeSet {α ι β : Type*} [DecidableEq β] (S : Finset α) (I : Finset ι) (key : ι → ℕ)
    (f : ι → α → β) (s : ι) (x : α) : Finset α :=
  S.filter (fun y => ∀ t ∈ I, key t < key s → f t y = f t x)

lemma mem_agreeSet {α ι β : Type*} [DecidableEq β] {S : Finset α} {I : Finset ι}
    {key : ι → ℕ} {f : ι → α → β} {s : ι} {x y : α} :
    y ∈ agreeSet S I key f s x ↔ y ∈ S ∧ ∀ t ∈ I, key t < key s → f t y = f t x :=
  mem_filter

/-- **Chain rule bound.** See the module docstring. -/
theorem chain_bound {α ι β : Type*} [DecidableEq α] [DecidableEq β] (key : ι → ℕ)
    (f : ι → α → β) (I : Finset ι) (S : Finset α) (hkey : Set.InjOn key I)
    (hdet : ∀ x ∈ S, ∀ y ∈ S, (∀ s ∈ I, f s x = f s y) → x = y) :
    (S.card : ℝ) * Real.log S.card ≤
      ∑ x ∈ S, ∑ s ∈ I, Real.log ((agreeSet S I key f s x).image (f s)).card := by
  classical
  unfold agreeSet
  induction hI : I.card generalizing I S with
  | zero =>
    rw [card_eq_zero] at hI
    subst hI
    have : S.card ≤ 1 := by
      rw [card_le_one]
      intro x hx y hy
      exact hdet x hx y hy (by simp)
    interval_cases h : S.card <;> simp
  | succ m ih =>
    have hne : I.Nonempty := by rw [← card_pos]; omega
    obtain ⟨s₀, hs₀, hmin⟩ := I.exists_min_image key hne
    set I' := I.erase s₀ with hI'
    have hI'card : I'.card = m := by rw [card_erase_of_mem hs₀]; omega
    have hkey' : Set.InjOn key I' := hkey.mono (by simp [hI', Set.subset_def]; tauto)
    have hlt : ∀ t ∈ I', key s₀ < key t := by
      intro t ht
      have ht' := mem_of_mem_erase ht
      have hne : t ≠ s₀ := ne_of_mem_erase ht
      rcases (hmin t ht').lt_or_eq with h | h
      · exact h
      · exact absurd (hkey ht' hs₀ h.symm) hne
    -- the fibres
    set P := S.image (f s₀) with hP
    set Sv : β → Finset α := fun v => S.filter (fun y => f s₀ y = v) with hSv
    -- term for s₀
    have hterm0 : ∀ x ∈ S, ((S.filter (fun y => ∀ t ∈ I, key t < key s₀ → f t y = f t x)).image
        (f s₀)).card = P.card := by
      intro x hx
      congr 2
      apply filter_true_of_mem
      intro y _ t ht h
      exact absurd h (not_lt.2 (hmin t ht))
    -- terms for s ∈ I'
    have hterm : ∀ x ∈ S, ∀ s ∈ I',
        (S.filter (fun y => ∀ t ∈ I, key t < key s → f t y = f t x)) =
        ((Sv (f s₀ x)).filter (fun y => ∀ t ∈ I', key t < key s → f t y = f t x)) := by
      intro x hx s hs
      ext y
      simp only [mem_filter, hSv]
      constructor
      · rintro ⟨hy, h⟩
        exact ⟨⟨hy, h s₀ hs₀ (hlt s hs)⟩, fun t ht => h t (mem_of_mem_erase ht)⟩
      · rintro ⟨⟨hy, h0⟩, h⟩
        refine ⟨hy, fun t ht htk => ?_⟩
        by_cases hts : t = s₀
        · subst hts; exact h0
        · exact h t (mem_erase.2 ⟨hts, ht⟩) htk
    have hsplit : ∀ x ∈ S, ∑ s ∈ I, Real.log
        ((S.filter (fun y => ∀ t ∈ I, key t < key s → f t y = f t x)).image (f s)).card =
        Real.log P.card + ∑ s ∈ I', Real.log
        (((Sv (f s₀ x)).filter (fun y => ∀ t ∈ I', key t < key s → f t y = f t x)).image
          (f s)).card := by
      intro x hx
      rw [← add_sum_erase I _ hs₀, hterm0 x hx]
      congr 1
      apply sum_congr rfl
      intro s hs
      rw [hterm x hx s hs]
    rw [sum_congr rfl hsplit, sum_add_distrib, sum_const, nsmul_eq_mul]
    -- regroup by fibres
    have hfib : ∑ x ∈ S, ∑ s ∈ I', Real.log
        (((Sv (f s₀ x)).filter (fun y => ∀ t ∈ I', key t < key s → f t y = f t x)).image
          (f s)).card =
        ∑ v ∈ P, ∑ x ∈ Sv v, ∑ s ∈ I', Real.log
        (((Sv v).filter (fun y => ∀ t ∈ I', key t < key s → f t y = f t x)).image
          (f s)).card := by
      rw [← sum_fiberwise_of_maps_to (s := S) (t := P) (g := f s₀)
        (fun x hx => mem_image_of_mem _ hx)]
      apply sum_congr rfl
      intro v _
      rw [sum_filter]
      simp only [hSv, sum_filter]
      apply sum_congr rfl
      intro x _
      split_ifs with h
      · rw [h]
      · rfl
    have hIH : ∀ v ∈ P, ((Sv v).card : ℝ) * Real.log (Sv v).card ≤
        ∑ x ∈ Sv v, ∑ s ∈ I', Real.log
        (((Sv v).filter (fun y => ∀ t ∈ I', key t < key s → f t y = f t x)).image
          (f s)).card := by
      intro v _
      apply ih I' (Sv v) hkey' _ hI'card
      intro x hx y hy h
      simp only [hSv, mem_filter] at hx hy
      apply hdet x hx.1 y hy.1
      intro s hs
      by_cases hss : s = s₀
      · subst hss; rw [hx.2, hy.2]
      · exact h s (mem_erase.2 ⟨hss, hs⟩)
    have hcard : S.card = ∑ v ∈ P, (Sv v).card := by
      rw [card_eq_sum_card_fiberwise (f := f s₀) (t := P) (fun x hx => mem_image_of_mem _ hx)]
    have hls := log_sum_ineq P (fun v => (Sv v).card)
    rw [← hcard] at hls
    rw [hfib]
    have := sum_le_sum hIH
    linarith

end LinialLuria
