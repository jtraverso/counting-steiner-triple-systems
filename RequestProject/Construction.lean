/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Core
public import RequestProject.Explicit
public import RequestProject.UpperBound
public import RequestProject.Latin

/-!
# Section 3 of the paper: the recursive construction

* `STS.D7_le` : inequality (3.3), `D₇(v) ≤ v^v N(v)`.
* `STS.construction_D7` : the construction in the proof of Lemma 3,
  `L(n) D₇(n + w)³ ≤ D₇(3n + w)` for `w ∈ {0, 1, 3, 7}`.
* `STS.lemma3` : Lemma 3, `D₇(v) ≥ L(n) D₇(u)³` with `(v+14)/3 ≥ u ≥ v/3 ≥ n ≥ (v-7)/3`.
* `STS.lemma4` : Lemma 4, `D₇(v) ≥ 1` for admissible `v ≥ 15`.
* `STS.sts_exists_iff` : STS's of order `v > 0` exist iff `v ≡ 1, 3 (mod 6)`.
-/

@[expose] public section

open Finset

namespace STS

lemma D7_eq_DSub (v : ℕ) : D7 v = DSub (Fin v) (fanoIn v) := rfl

/-- The blocks of the fixed STS of order 7 through two points `< w` stay below `w`, for
`w ∈ {0, 1, 3, 7}`. -/
lemma fano_covers : ∀ w ∈ ({0, 1, 3, 7} : Finset ℕ), ∀ a a' : Fin 7, (a : ℕ) < w →
    (a' : ℕ) < w → a ≠ a' → ∃ F ∈ fano, a ∈ F ∧ a' ∈ F ∧ ∀ z ∈ F, (z : ℕ) < w := by
  decide

lemma finSumFinEquiv_symm_castLE_of_lt {w n : ℕ} (h : 7 ≤ w + n) (k : Fin 7) (hk : (k : ℕ) < w) :
    (finSumFinEquiv (m := w) (n := n)).symm (Fin.castLE h k) = Sum.inl ⟨k, hk⟩ := by
  have : Fin.castLE h k = Fin.castAdd n ⟨k, hk⟩ := Fin.ext rfl
  rw [this, finSumFinEquiv_symm_apply_castAdd]

/-- **The construction of Lemma 3**: for `w ∈ {0, 1, 3, 7}` and `n + w ≥ 7`,
`L(n) D₇(n + w)³ ≤ D₇(3n + w)`. -/
theorem construction_D7 (w n : ℕ) (hw : w ∈ ({0, 1, 3, 7} : Finset ℕ)) (hn : 7 ≤ w + n) :
    L n * D7 (w + n) ^ 3 ≤ D7 (3 * n + w) := by
  have hw7 : w ≤ 7 := by simp only [mem_insert, mem_singleton] at hw; omega
  have h1 : 7 ≤ 3 * n + w := by omega
  set G : Finset (Finset (Fin w ⊕ Fin n)) :=
    mapBlocks (finSumFinEquiv (m := w) (n := n)).symm (fanoIn (w + n)) with hGdef
  have hY : DSub (Fin w ⊕ Fin n) G = D7 (w + n) := by
    rw [D7_eq_DSub, ← DSub_equiv finSumFinEquiv G, hGdef]
    congr 1
    have := mapBlocks_symm_mapBlocks (finSumFinEquiv (m := w) (n := n)).symm (fanoIn (w + n))
    simpa using this
  have hG : Construction.CoversW G := by
    intro a a' haa
    have hne : (⟨a, by omega⟩ : Fin 7) ≠ ⟨a', by omega⟩ := by
      intro h; apply haa; exact Fin.ext (by simpa using congrArg Fin.val h)
    obtain ⟨F, hF, ha, ha', hlt⟩ := fano_covers w hw ⟨a, by omega⟩ ⟨a', by omega⟩ a.2 a'.2 hne
    refine ⟨(F.image (Fin.castLE hn)).image (finSumFinEquiv (m := w) (n := n)).symm, ?_, ?_, ?_, ?_⟩
    · rw [hGdef, fanoIn, dif_pos hn]
      exact mem_image_of_mem _ (mem_image_of_mem _ hF)
    · refine mem_image.2 ⟨Fin.castLE hn ⟨a, by omega⟩, mem_image_of_mem _ ha, ?_⟩
      rw [finSumFinEquiv_symm_castLE_of_lt hn _ a.2]
    · refine mem_image.2 ⟨Fin.castLE hn ⟨a', by omega⟩, mem_image_of_mem _ ha', ?_⟩
      rw [finSumFinEquiv_symm_castLE_of_lt hn _ a'.2]
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hz
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hy
      rw [finSumFinEquiv_symm_castLE_of_lt hn _ (hlt k hk)]
      rfl
  let e : Fin w ⊕ (Fin 3 × Fin n) ≃ Fin (3 * n + w) :=
    (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by ring)))
  have hval : ∀ k : Fin 7,
      ((e (Construction.ι 0 ((finSumFinEquiv (m := w) (n := n)).symm (Fin.castLE hn k)))) : ℕ) =
        k := by
    intro k
    rcases lt_or_ge (k : ℕ) w with hk | hk
    · have : Fin.castLE hn k = Fin.castAdd n ⟨k, hk⟩ := Fin.ext rfl
      rw [this, finSumFinEquiv_symm_apply_castAdd]
      simp [e, Construction.ι]
    · have : Fin.castLE hn k = Fin.natAdd w ⟨k - w, by omega⟩ := Fin.ext (by simp; omega)
      rw [this, finSumFinEquiv_symm_apply_natAdd]
      simp [e, Construction.ι, finProdFinEquiv]
      omega
  have hX : DSub (Fin w ⊕ (Fin 3 × Fin n)) (mapBlocks (Construction.ι 0) G) =
      D7 (3 * n + w) := by
    rw [D7_eq_DSub, ← DSub_equiv e]
    congr 1
    rw [hGdef, fanoIn, fanoIn, dif_pos hn, dif_pos h1, mapBlocks_comp, mapBlocks_comp,
      mapBlocks_comp]
    congr 1
    funext k
    exact Fin.ext (hval k)
  rw [← hY, ← hX]
  exact Construction.card_le hG

/-- The choice of `n` and `w` (with `u = n + w`) in the proof of Lemma 3. -/
lemma table (v : ℕ) (hv : 15 ≤ v) (ha : Admissible v) :
    ∃ n w, w ∈ ({0, 1, 3, 7} : Finset ℕ) ∧ v = 3 * n + w ∧ Admissible (n + w) ∧ 7 ≤ n + w ∧
      ((n + w = 9 ∨ n + w = 13) → v = 25 ∨ v = 27 ∨ v = 33 ∨ v = 37 ∨ v = 39) := by
  unfold Admissible at *
  have h18 : v % 18 = 1 ∨ v % 18 = 3 ∨ v % 18 = 7 ∨ v % 18 = 9 ∨ v % 18 = 13 ∨
      v % 18 = 15 := by omega
  rcases h18 with h | h | h | h | h | h
  · exact ⟨6 * (v / 18), 1, by simp, by omega, by omega, by omega, by omega⟩
  · exact ⟨6 * (v / 18) + 1, 0, by simp, by omega, by omega, by omega, by omega⟩
  · exact ⟨6 * (v / 18) + 2, 1, by simp, by omega, by omega, by omega, by omega⟩
  · exact ⟨6 * (v / 18) + 3, 0, by simp, by omega, by omega, by omega, by omega⟩
  · exact ⟨6 * (v / 18) + 2, 7, by simp, by omega, by omega, by omega, by omega⟩
  · exact ⟨6 * (v / 18) + 4, 3, by simp, by omega, by omega, by omega, by omega⟩

/-- **Lemma 3.** Given admissible `v ≥ 19`, there exist admissible `u` and `n` such that
`D₇(v) ≥ L(n) D₇(u)³` and `(v + 14)/3 ≥ u ≥ v/3 ≥ n ≥ (v - 7)/3`. -/
theorem lemma3 (v : ℕ) (hv : 19 ≤ v) (ha : Admissible v) :
    ∃ u n : ℕ, Admissible u ∧ L n * D7 u ^ 3 ≤ D7 v ∧
      (u : ℝ) ≤ ((v : ℝ) + 14) / 3 ∧ (v : ℝ) / 3 ≤ u ∧ (n : ℝ) ≤ (v : ℝ) / 3 ∧
      ((v : ℝ) - 7) / 3 ≤ n := by
  obtain ⟨n, w, hw, hv', hu, hu7, -⟩ := table v (by omega) ha
  have hw7 : w ≤ 7 := by simp only [mem_insert, mem_singleton] at hw; omega
  refine ⟨n + w, n, hu, ?_, ?_, ?_, ?_, ?_⟩
  · have := construction_D7 w n hw (by omega)
    rw [show w + n = n + w by ring, ← hv'] at this
    exact this
  all_goals
    have hvr : (v : ℝ) = 3 * n + w := by exact_mod_cast hv'
    have hwr : (w : ℝ) ≤ 7 := by exact_mod_cast hw7
    have hw0 : (0 : ℝ) ≤ w := by positivity
    push_cast
    rw [hvr]
    linarith

lemma L_pos (n : ℕ) : 1 ≤ L n := by
  refine le_trans ?_ (theoremA n)
  exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 (fun i _ => Nat.factorial_ne_zero _))

lemma D7_pos_of {v : ℕ} {B : Finset (Finset (Fin v))} (hB : IsSTS B) (hF : fanoIn v ⊆ B) :
    1 ≤ D7 v := by
  rw [D7, Nat.one_le_iff_ne_zero, Nat.card_ne_zero]
  exact ⟨⟨⟨B, hB, hF⟩⟩, inferInstance⟩

/-- **Lemma 4.** For admissible `v ≥ 15`, `D₇(v) ≥ 1`, i.e. there is an STS of order `v`
containing a prescribed STS of order 7 on a prescribed 7-subset. (The paper cites the literature
for this; here it is proved by the recursive construction of Lemma 3, together with explicit
systems of orders 25, 27, 33, 37 and 39.) -/
theorem lemma4 (v : ℕ) (hv : 15 ≤ v) (ha : Admissible v) : 1 ≤ D7 v := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  by_cases hbad : v = 25 ∨ v = 27 ∨ v = 33 ∨ v = 37 ∨ v = 39
  · rcases hbad with rfl | rfl | rfl | rfl | rfl
    · exact D7_pos_of isSTS_ofTriples25 fanoIn_subset25
    · exact D7_pos_of isSTS_ofTriples27 fanoIn_subset27
    · exact D7_pos_of isSTS_ofTriples33 fanoIn_subset33
    · exact D7_pos_of isSTS_ofTriples37 fanoIn_subset37
    · exact D7_pos_of isSTS_ofTriples39 fanoIn_subset39
  obtain ⟨n, w, hw, hv', hu, hu7, hbadu⟩ := table v hv ha
  have hw7 : w ≤ 7 := by simp only [mem_insert, mem_singleton] at hw; omega
  have hu' : 1 ≤ D7 (n + w) := by
    by_cases h7 : n + w = 7
    · rw [h7]; exact D7_pos_of isSTS_fanoIn7 (subset_refl _)
    · have h15 : 15 ≤ n + w := by
        unfold Admissible at hu
        have : ¬ (n + w = 9 ∨ n + w = 13) := fun h => hbad (hbadu h)
        omega
      exact ih (n + w) (by omega) h15 hu
  have := construction_D7 w n hw (by omega)
  rw [show w + n = n + w by ring, ← hv'] at this
  refine le_trans ?_ this
  have h1 := L_pos n
  have h2 : 1 ≤ D7 (n + w) ^ 3 := Nat.one_le_pow _ _ hu'
  nlinarith

/-- Inequality (3.3): `D₇(v) ≤ v^v N(v)`. -/
theorem D7_le (v : ℕ) : D7 v ≤ v ^ v * N v := by
  have h1 : D7 v ≤ D v := by
    unfold D7 D
    exact Nat.card_le_card_of_injective (fun B => ⟨B.1, B.2.1⟩) (fun B B' h => by
      apply Subtype.ext; have := congrArg Subtype.val h; exact this)
  calc D7 v ≤ D v := h1
    _ ≤ v.factorial * N v := D_le_factorial_mul_N v
    _ ≤ v ^ v * N v := Nat.mul_le_mul_right _ (Nat.factorial_le_pow v)

/-- Every point of an STS on `Fin v` lies in `(v - 1)/2` blocks; in particular `v` is odd. -/
lemma odd_of_isSTS {v : ℕ} (hv : 0 < v) {B : Finset (Finset (Fin v))} (hB : IsSTS B) :
    v % 2 = 1 := by
  let x : Fin v := ⟨0, hv⟩
  set Bx := B.filter (fun A => x ∈ A)
  have hU : Bx.biUnion (fun A => A.erase x) = univ.erase x := by
    ext y
    simp only [mem_biUnion, mem_erase, mem_univ, and_true, Bx, mem_filter]
    constructor
    · rintro ⟨A, -, hyx, -⟩; exact hyx
    · intro hyx
      obtain ⟨A, ⟨hA, hxA, hyA⟩, -⟩ := hB.2 x y (Ne.symm hyx)
      exact ⟨A, ⟨hA, hxA⟩, hyx, hyA⟩
  have hcard := congrArg Finset.card hU
  rw [card_biUnion, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hcard
  · rw [sum_const_nat (m := 2)] at hcard
    · omega
    · intro A hA
      simp only [Bx, mem_filter] at hA
      rw [card_erase_of_mem hA.2, hB.1 A hA.1]
  · intro A hA A' hA' hne
    simp only [Bx, coe_filter, Set.mem_setOf_eq] at hA hA'
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨hyx, hyA⟩ := mem_erase.1 hy
    obtain ⟨-, hyA'⟩ := mem_erase.1 hy'
    have := inter_card_le_one hB hA.1 hA'.1 hne
    have : ({x, y} : Finset (Fin v)) ⊆ A ∩ A' := by
      intro z hz; simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact mem_inter.2 ⟨hA.2, hA'.2⟩
      · exact mem_inter.2 ⟨hyA, hyA'⟩
    have := card_le_card this
    rw [card_pair (Ne.symm hyx)] at this
    omega

/-- Steiner triple systems of order `v > 0` exist if and only if `v ≡ 1` or `3 (mod 6)`. -/
theorem sts_exists_iff (v : ℕ) (hv : 0 < v) :
    (∃ B : Finset (Finset (Fin v)), IsSTS B) ↔ Admissible v := by
  constructor
  · rintro ⟨B, hB⟩
    have hodd := odd_of_isSTS hv hB
    have h3 := three_mul_card_blocks hB
    rw [Fintype.card_fin, Nat.choose_two_right] at h3
    obtain ⟨m, rfl⟩ : ∃ m, v = 2 * m + 1 := ⟨v / 2, by omega⟩
    have h2 : (2 * m + 1) * (2 * m + 1 - 1) / 2 = m * (2 * m + 1) := by
      rw [show 2 * m + 1 - 1 = 2 * m by omega,
        show (2 * m + 1) * (2 * m) = 2 * (m * (2 * m + 1)) by ring]
      omega
    rw [h2] at h3
    have hmod : (m * (2 * m + 1)) % 3 = 0 := by omega
    unfold Admissible
    have : m % 3 ≠ 2 := by
      intro hm
      rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod 2, hm] at hmod
      norm_num at hmod
    omega
  · intro ha
    by_cases h15 : 15 ≤ v
    · have := lemma4 v h15 ha
      rw [D7, Nat.one_le_iff_ne_zero, Nat.card_ne_zero] at this
      obtain ⟨⟨B, hB, -⟩⟩ := this.1
      exact ⟨B, hB⟩
    · unfold Admissible at ha
      have : v = 1 ∨ v = 3 ∨ v = 7 ∨ v = 9 ∨ v = 13 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, isSTS_empty1⟩
      · exact ⟨_, isSTS_ofTriples3⟩
      · exact ⟨_, isSTS_fano⟩
      · exact ⟨_, isSTS_ofTriples9⟩
      · exact ⟨_, isSTS_ofTriples13⟩

end STS
