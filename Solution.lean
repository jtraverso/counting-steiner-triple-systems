/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import RequestProject.Main

/-!
# Counting Steiner triple systems: Wilson (1974) and Linial–Luria (2013)

A Steiner triple system (STS) on `Fin v` is a family of 3-subsets such that any two distinct
points lie in exactly one member (`CountingSTS.IsSTS`). `N v` is the number of isomorphism classes
of STS of order `v`, `D v` the number of STS on the fixed set `Fin v`, `L n` the number of Latin
squares of order `n`, and `F n` the number of proper `(n − 1)`-edge-colourings of `K_n`
(ordered 1-factorizations).

**R. M. Wilson, *Nonisomorphic Steiner triple systems*, Math. Z. 135 (1974) 303–313.**
* (2.1) `N_le_D`, `D_le_factorial_mul_N`: `N v ≤ D v ≤ v! N v`.
* Theorem 1, `theorem1`: `N v < (e^{-1/2} v)^{v²/6}` for `v ≥ 7`.
* Lemma 3, `lemma3`: the recursive construction `D₇(v) ≥ L(n) D₇(u)³`.
* Lemma 4, `lemma4`: every admissible `v ≥ 15` has an STS containing the fixed STS(7).
* Lemma 5, `lemma5_i`, `lemma5_ii`, `lemma5_iii`: `L(6) = 6!5!·9408`, `L(7) = 7!6!·16942080`,
  `L(8) = 8!7!·535281401856`.
* Theorem 2, `theorem2`: `N v ≥ (e^{-5} v)^{v²/12}` for admissible `v`; `theorem2_vdW`: exponent
  `v²/6` under the van der Waerden permanent conjecture (`vdWPC`, an explicit hypothesis).
* Theorem 3, `theorem3` and `theorem3_vdW`: the asymptotic lower bounds with constant
  `3^{-3/2} e^{-2} − ε`.
* `van_der_waerden`: the van der Waerden permanent conjecture `vdWPC` holds (Egorychev 1981,
  Falikman 1981; proved following Gurvits as simplified by Laurent–Schrijver), hence
  `theorem2_full` and `theorem3_full`: the bounds with exponent `v²/6` hold unconditionally.
* Theorem 4, `theorem4_i`, `theorem4_ii`, `theorem4_iii`: `N(19) ≥ 2450`, `N(21) ≥ 2160980`,
  `N(25) ≥ 163929929318400`.

**N. Linial, Z. Luria, *An upper bound on the number of Steiner triple systems*, Random
Structures Algorithms 43 (2013) 399–406.**
* Theorem 1.1, `theorem_1_1` (and the explicit `sts_upper_bound_explicit`):
  `D n ≤ ((1 + ε) n / e²)^{n²/6}` for every `ε > 0` and large `n`.
* Theorem 1.2, `theorem_1_2` (and `oneFactorization_upper_bound_explicit`):
  `F n ≤ ((1 + ε) n / e²)^{n²/2}`.

The Mathlib definitions used here are reproduced verbatim in `MATHLIB_DEFINITIONS.md`.
-/

@[expose] public section

open Finset Filter

namespace CountingSTS


variable {α : Type*} [DecidableEq α]

/-- `B` is a Steiner triple system on the point type `α`: every block is a 3-subset, and
any two distinct points lie in exactly one block. -/
def IsSTS (B : Finset (Finset α)) : Prop :=
  (∀ A ∈ B, A.card = 3) ∧ ∀ x y : α, x ≠ y → ∃! A, A ∈ B ∧ x ∈ A ∧ y ∈ A

/-- The image of a family of blocks under a map of points. -/
def mapBlocks {β : Type*} [DecidableEq β] (f : α → β) (B : Finset (Finset α)) :
    Finset (Finset β) :=
  B.image (fun A => A.image f)

/-- Two families of blocks on `Fin v` are isomorphic if some permutation of the points
maps the blocks of the first onto the blocks of the second. -/
def Iso {v : ℕ} (B₁ B₂ : Finset (Finset (Fin v))) : Prop :=
  ∃ σ : Equiv.Perm (Fin v), mapBlocks σ B₁ = B₂

/-- The STS's on the point set `Fin v`. -/
abbrev STSOn (v : ℕ) := {B : Finset (Finset (Fin v)) // IsSTS B}

lemma mapBlocks_id (B : Finset (Finset α)) : mapBlocks id B = B := by
  simp [mapBlocks]

omit [DecidableEq α] in
lemma mapBlocks_comp {β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ] (f : α → β)
    (g : β → γ) (B : Finset (Finset α)) : mapBlocks g (mapBlocks f B) = mapBlocks (g ∘ f) B := by
  simp only [mapBlocks, Finset.image_image]
  congr 1
  funext A
  simp [Finset.image_image]

theorem iso_refl {v : ℕ} (B : STSOn v) : Iso B.1 B.1 :=
  ⟨1, by simpa using mapBlocks_id B.1⟩

theorem iso_symm {v : ℕ} {B₁ B₂ : STSOn v} (h : Iso B₁.1 B₂.1) : Iso B₂.1 B₁.1 := by
  obtain ⟨σ, h⟩ := h
  refine ⟨σ⁻¹, ?_⟩
  rw [← h, mapBlocks_comp]
  convert mapBlocks_id B₁.1
  funext x; simp

theorem iso_trans {v : ℕ} {B₁ B₂ B₃ : STSOn v} (h : Iso B₁.1 B₂.1) (h' : Iso B₂.1 B₃.1) :
    Iso B₁.1 B₃.1 := by
  obtain ⟨σ, h⟩ := h
  obtain ⟨τ, h'⟩ := h'
  refine ⟨τ * σ, ?_⟩
  rw [← h', ← h, mapBlocks_comp]
  rfl

/-- Isomorphism is an equivalence relation on STS's of order `v`. -/
instance isoSetoid (v : ℕ) : Setoid (STSOn v) where
  r B₁ B₂ := Iso B₁.1 B₂.1
  iseqv := ⟨iso_refl, iso_symm, iso_trans⟩

/-- `N v`: the number of pairwise nonisomorphic Steiner triple systems of order `v`. -/
noncomputable def N (v : ℕ) : ℕ := Nat.card (Quotient (isoSetoid v))

/-- `D v`: the number of distinct classes of 3-subsets `B` of the fixed `v`-set `Fin v`
such that `(Fin v, B)` is an STS. -/
noncomputable def D (v : ℕ) : ℕ := Nat.card (STSOn v)

/-- A Latin square of order `n`: a map `l : rows × columns → symbols` (all three sets being
`Fin n`) such that each row and each column contains each symbol exactly once. -/
def IsLatin {n : ℕ} (l : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Function.Bijective (l i)) ∧ ∀ j, Function.Bijective (fun i => l i j)

/-- `L n`: the number of Latin squares of order `n`. -/
noncomputable def L (n : ℕ) : ℕ := Nat.card {l : Fin n → Fin n → Fin n // IsLatin l}

/-- A fixed Steiner triple system of order 7 (the Fano plane) on `Fin 7`. -/
def fano : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

/-- The fixed STS of order 7 placed on the points `0, …, 6` of `Fin v` (empty if `v < 7`). -/
def fanoIn (v : ℕ) : Finset (Finset (Fin v)) :=
  if h : 7 ≤ v then mapBlocks (Fin.castLE h) fano else ∅

/-- `D7 v`: the number of STS's on `Fin v` containing the fixed STS of order 7 on the
7-subset `{0, …, 6}`. -/
noncomputable def D7 (v : ℕ) : ℕ :=
  Nat.card {B : Finset (Finset (Fin v)) // IsSTS B ∧ fanoIn v ⊆ B}

/-- The van der Waerden permanent conjecture: the permanent of a doubly stochastic matrix
of order `n` is at least `n! / n^n`. -/
def vdWPC : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ), M ∈ doublyStochastic ℝ (Fin n) →
    (Nat.factorial n : ℝ) / (n : ℝ) ^ n ≤ M.permanent

/-- `v` is admissible: `v ≡ 1` or `3 (mod 6)`. -/
def Admissible (v : ℕ) : Prop := v % 6 = 1 ∨ v % 6 = 3

/-- The number `F(n)` of 1-factorizations of `K_n`: proper edge colourings of the complete
graph `K_n` with the `n - 1` colours `Fin (n - 1)`. -/
noncomputable def F (n : ℕ) : ℕ :=
  Nat.card ((⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin (n - 1)))

/-- Inequality (2.1), left half: `N(v) ≤ D(v)`. -/
theorem N_le_D (v : ℕ) : N v ≤ D v :=
  STS.N_le_D v

/-- Inequality (2.1), right half: `D(v) ≤ v! N(v)`. -/
theorem D_le_factorial_mul_N (v : ℕ) : D v ≤ v.factorial * N v :=
  STS.D_le_factorial_mul_N v

/-- **Theorem 1.** For every `v ≥ 7`, `N(v) < (e^{-1/2} v)^{v²/6}`. -/
theorem theorem1 (v : ℕ) (hv : 7 ≤ v) :
    (N v : ℝ) < (Real.exp (-1 / 2) * v) ^ ((v : ℝ) ^ 2 / 6) :=
  STS.theorem1 v hv

/-- **Lemma 3.** Given admissible `v ≥ 19`, there exist admissible `u` and `n` such that
`D₇(v) ≥ L(n) D₇(u)³` and `(v + 14)/3 ≥ u ≥ v/3 ≥ n ≥ (v - 7)/3`. -/
theorem lemma3 (v : ℕ) (hv : 19 ≤ v) (ha : Admissible v) :
    ∃ u n : ℕ, Admissible u ∧ L n * D7 u ^ 3 ≤ D7 v ∧
      (u : ℝ) ≤ ((v : ℝ) + 14) / 3 ∧ (v : ℝ) / 3 ≤ u ∧ (n : ℝ) ≤ (v : ℝ) / 3 ∧
      ((v : ℝ) - 7) / 3 ≤ n :=
  STS.lemma3 v hv ha

/-- **Lemma 4.** For admissible `v ≥ 15`, `D₇(v) ≥ 1`, i.e. there is an STS of order `v`
containing a prescribed STS of order 7 on a prescribed 7-subset. (The paper cites the literature
for this; here it is proved by the recursive construction of Lemma 3, together with explicit
systems of orders 25, 27, 33, 37 and 39.) -/
theorem lemma4 (v : ℕ) (hv : 15 ≤ v) (ha : Admissible v) : 1 ≤ D7 v :=
  STS.lemma4 v hv ha

/-- **Lemma 5 (i).** `L(6) = 6! 5! · 9408`. -/
theorem lemma5_i : L 6 = Nat.factorial 6 * Nat.factorial 5 * 9408 :=
  STS.lemma5_i

/-- **Lemma 5 (ii).** `L(7) = 7! 6! · 16942080`. -/
theorem lemma5_ii : L 7 = Nat.factorial 7 * Nat.factorial 6 * 16942080 :=
  STS.lemma5_ii

/-- **Lemma 5 (iii).** `L(8) = 8! 7! · 535281401856`. -/
theorem lemma5_iii : L 8 = Nat.factorial 8 * Nat.factorial 7 * 535281401856 :=
  STS.lemma5_iii

/-- **Theorem 2**, first part (inequality (1.3)): `N(v) ≥ (e^{-5} v)^{v²/12}`. -/
theorem theorem2 (v : ℕ) (hv : Admissible v) :
    (Real.exp (-5) * v) ^ ((v : ℝ) ^ 2 / 12) ≤ N v :=
  STS.theorem2 v hv

/-- **Theorem 2**, second part: if the vdWPC is valid, `N(v) ≥ (e^{-5} v)^{v²/6}`. -/
theorem theorem2_vdW (h : vdWPC) (v : ℕ) (hv : Admissible v) :
    (Real.exp (-5) * v) ^ ((v : ℝ) ^ 2 / 6) ≤ N v :=
  STS.theorem2_vdW h v hv

/-- **Theorem 3**, first part: for any `ε > 0` (small enough that the base is positive) and all
sufficiently large admissible `v`, `N(v) ≥ ((3^{-3/2} e^{-2} - ε) v)^{v²/12}`. -/
theorem theorem3 (ε : ℝ) (hε : 0 < ε) (hε' : ε < (3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2)) :
    ∀ᶠ v : ℕ in atTop, Admissible v →
      (((3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2) - ε) * v) ^ ((v : ℝ) ^ 2 / 12) ≤ N v :=
  STS.theorem3 ε hε hε'

/-- **Theorem 3**, second part (inequality (1.2)): if the vdWPC is valid, then for any `ε > 0`
(small enough that the base is positive) and all sufficiently large admissible `v`,
`N(v) ≥ ((3^{-3/2} e^{-2} - ε) v)^{v²/6}`. -/
theorem theorem3_vdW (h : vdWPC) (ε : ℝ) (hε : 0 < ε)
    (hε' : ε < (3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2)) :
    ∀ᶠ v : ℕ in atTop, Admissible v →
      (((3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2) - ε) * v) ^ ((v : ℝ) ^ 2 / 6) ≤ N v :=
  STS.theorem3_vdW h ε hε hε'

/-- **The van der Waerden permanent theorem** (Egorychev 1981, Falikman 1981): the permanent
of a doubly stochastic `n × n` matrix is at least `n!/n^n`, i.e. `vdWPC` holds. -/
theorem van_der_waerden : vdWPC :=
  STS.van_der_waerden

/-- **Theorem 2**, second part, unconditionally: `N(v) ≥ (e^{-5} v)^{v²/6}`. -/
theorem theorem2_full (v : ℕ) (hv : Admissible v) :
    (Real.exp (-5) * v) ^ ((v : ℝ) ^ 2 / 6) ≤ N v :=
  STS.theorem2_full v hv

/-- **Theorem 3**, second part (inequality (1.2)), unconditionally: for any `ε > 0` (small enough
that the base is positive) and all sufficiently large admissible `v`,
`N(v) ≥ ((3^{-3/2} e^{-2} - ε) v)^{v²/6}`. -/
theorem theorem3_full (ε : ℝ) (hε : 0 < ε) (hε' : ε < (3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2)) :
    ∀ᶠ v : ℕ in Filter.atTop, Admissible v →
      (((3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2) - ε) * v) ^ ((v : ℝ) ^ 2 / 6) ≤ N v :=
  STS.theorem3_full ε hε hε'

/-- **Theorem 4 (i).** `N(19) ≥ 2450`. -/
theorem theorem4_i : 2450 ≤ N 19 :=
  STS.theorem4_i

/-- **Theorem 4 (ii).** `N(21) ≥ 2160980`. -/
theorem theorem4_ii : 2160980 ≤ N 21 :=
  STS.theorem4_ii

/-- **Theorem 4 (iii).** `N(25) ≥ 163929929318400`. -/
theorem theorem4_iii : 163929929318400 ≤ N 25 :=
  STS.theorem4_iii

/-- **Theorem 1.1, explicit form**: for `n ≥ 4`,
`STS(n) ≤ exp ((n (n-1) / 6) · (log n - 2 + 1200 / √(n-3)))`. -/
theorem sts_upper_bound_explicit (n : ℕ) (hn : 4 ≤ n) :
    (D n : ℝ) ≤
      Real.exp ((n * (n - 1) / 6 : ℝ) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 3))) :=
  LinialLuria.sts_upper_bound_explicit n hn

/-- **Theorem 1.1** (Linial–Luria): `STS(n) ≤ ((1 + o(1)) n / e²)^{n²/6}`; that is, for every
`ε > 0` and all sufficiently large `n`, `STS(n) ≤ ((1 + ε) n / e²)^{n²/6}`. -/
theorem theorem_1_1 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (D n : ℝ) ≤ ((1 + ε) * n / Real.exp 2) ^ ((n : ℝ) ^ 2 / 6) :=
  LinialLuria.theorem_1_1 ε hε

/-- **Theorem 1.2, explicit form**: for `n ≥ 3`,
`F(n) ≤ exp ((n (n-1) / 2) · (log n - 2 + 1200 / √(n-2)))`. -/
theorem oneFactorization_upper_bound_explicit (n : ℕ) (hn : 3 ≤ n) :
    (F n : ℝ) ≤
      Real.exp ((n * (n - 1) / 2 : ℝ) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 2))) :=
  LinialLuria.oneFactorization_upper_bound_explicit n hn

/-- **Theorem 1.2** (Linial–Luria): `F(n) ≤ ((1 + o(1)) n / e²)^{n²/2}`; that is, for every
`ε > 0` and all sufficiently large `n`, `F(n) ≤ ((1 + ε) n / e²)^{n²/2}`. -/
theorem theorem_1_2 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (F n : ℝ) ≤ ((1 + ε) * n / Real.exp 2) ^ ((n : ℝ) ^ 2 / 2) :=
  LinialLuria.theorem_1_2 ε hε

end CountingSTS
