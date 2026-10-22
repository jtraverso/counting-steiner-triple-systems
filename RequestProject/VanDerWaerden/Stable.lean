/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.VanDerWaerden.Univariate

/-!
# Real stable polynomials (in the form needed for Gurvits's proof)

For a real multivariate polynomial `Q` in the variables `Fin n` we consider

* `VdW.CStable Q` : `Q(z) ≠ 0` whenever all `Im zⱼ > 0` (real stability);
* `VdW.CMono Q` : `‖Q(z)‖ ≤ ‖Q(z + i v)‖` whenever all `Im zⱼ ≥ 0` and all `vⱼ ≥ 0`
  (a closed condition, which replaces Hurwitz's theorem);
* `VdW.PosOn Q` : `Q(x) > 0` on the open positive orthant.

Main facts: `CMono` and `PosOn` imply `CStable` (`stable_of_mono_pos`), `CStable` implies `CMono`
(`mono_of_stable`), `CStable` is preserved by partial derivatives in a variable in which the
polynomial is nonconstant along every line (`stable_pderiv`, Gauss–Lucas), and restrictions of
`CMono` polynomials to real lines in nonnegative directions are real-rooted
(`roots_im_eq_zero_of_mono`).
-/

@[expose] public section

open Polynomial Complex

namespace VdW

variable {n : ℕ}

/-- The restriction `t ↦ Q(z + t w)` of `Q` to a line, as a univariate polynomial. -/
noncomputable def line {R : Type*} [CommRing R] [Algebra ℝ R] (z w : Fin n → R)
    (Q : MvPolynomial (Fin n) ℝ) : R[X] :=
  MvPolynomial.aeval (fun j => C (z j) + C (w j) * X) Q

lemma eval_line {R : Type*} [CommRing R] [Algebra ℝ R] (z w : Fin n → R)
    (Q : MvPolynomial (Fin n) ℝ) (t : R) :
    (line z w Q).eval t = MvPolynomial.aeval (fun j => z j + w j * t) Q := by
  unfold line
  induction Q using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma eval_line_single {R : Type*} [CommRing R] [Algebra ℝ R] (z : Fin n → R) (k : Fin n)
    (Q : MvPolynomial (Fin n) ℝ) (t : R) :
    (line z (Pi.single k 1) Q).eval t = MvPolynomial.aeval (Function.update z k (z k + t)) Q := by
  rw [eval_line]
  refine congrArg (fun f => MvPolynomial.aeval f Q) (funext fun j => ?_)
  rcases eq_or_ne j k with rfl | hjk
  · simp
  · simp [hjk]

lemma map_line (x w : Fin n → ℝ) (Q : MvPolynomial (Fin n) ℝ) :
    (line x w Q).map (algebraMap ℝ ℂ) =
      line (fun j => (x j : ℂ)) (fun j => (w j : ℂ)) Q := by
  unfold line
  induction Q using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Polynomial.map_mul]

lemma aeval_ofReal (x : Fin n → ℝ) (Q : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (fun j => (x j : ℂ)) Q = (MvPolynomial.eval x Q : ℂ) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma line_derivative {R : Type*} [CommRing R] [Algebra ℝ R] (z : Fin n → R) (k : Fin n)
    (Q : MvPolynomial (Fin n) ℝ) :
    derivative (line z (Pi.single k 1) Q) =
      line z (Pi.single k 1) (MvPolynomial.pderiv k Q) := by
  unfold line
  induction Q using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, derivative_mul, hp, Derivation.leibniz,
      MvPolynomial.pderiv_X, smul_eq_mul, map_add]
    rcases eq_or_ne i k with rfl | hik
    · simp; ring
    · simp [Pi.single_apply, hik]; ring

/-- Real stability: `Q` does not vanish when all variables are in the open upper half-plane. -/
def CStable (Q : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ z : Fin n → ℂ, (∀ j, 0 < (z j).im) → MvPolynomial.aeval z Q ≠ 0

/-- Monotonicity of `‖Q‖` in the imaginary directions on the closed upper half-plane. -/
def CMono (Q : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ (z : Fin n → ℂ) (v : Fin n → ℝ), (∀ j, 0 ≤ (z j).im) → (∀ j, 0 ≤ v j) →
    ‖MvPolynomial.aeval z Q‖ ≤ ‖MvPolynomial.aeval (fun j => z j + v j * I) Q‖

/-- Positivity on the open positive orthant. -/
def PosOn (Q : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, (∀ j, 0 < x j) → 0 < MvPolynomial.eval x Q

lemma infinite_Icc_mul_I (a b : ℝ) (hab : a < b) (c : ℂ) :
    Set.Infinite ((fun s : ℝ => c + (s : ℂ) * I) '' Set.Icc a b) := by
  apply Set.Infinite.image _ (Set.Icc_infinite hab)
  intro s _ t _ hst
  have := congrArg Complex.im hst
  simpa using this

/-- A `CMono` polynomial which is positive on the positive orthant is real stable. -/
theorem stable_of_mono_pos {Q : MvPolynomial (Fin n) ℝ} (hM : CMono Q) (hP : PosOn Q) :
    CStable Q := by
  intro z hz h0
  set x0 : Fin n → ℝ := fun j => (z j).re with hx0
  set y0 : Fin n → ℝ := fun j => (z j).im with hy0
  set P := line (fun j => (x0 j : ℂ)) (fun j => (y0 j : ℂ)) Q with hPdef
  have hroot : ∀ s ∈ Set.Icc (0 : ℝ) 1, P.IsRoot (0 + (s : ℂ) * I) := by
    intro s hs
    rw [IsRoot, eval_line]
    have hle := hM (fun j => (x0 j : ℂ) + ((s * y0 j : ℝ) : ℂ) * I) (fun j => (1 - s) * y0 j)
      (fun j => by simpa using mul_nonneg hs.1 (hz j).le)
      (fun j => mul_nonneg (by linarith [hs.2]) (hz j).le)
    have e1 : (fun j => (x0 j : ℂ) + ((s * y0 j : ℝ) : ℂ) * I + (((1 - s) * y0 j : ℝ) : ℂ) * I)
        = z := by
      funext j; apply Complex.ext <;> simp [hx0, hy0]; ring
    rw [e1, h0, norm_zero] at hle
    have e2 : (fun j => (x0 j : ℂ) + (y0 j : ℂ) * (0 + (s : ℂ) * I)) =
        (fun j => (x0 j : ℂ) + ((s * y0 j : ℝ) : ℂ) * I) := by
      funext j; push_cast; ring
    rw [e2]; exact norm_le_zero_iff.1 hle
  have hP0 : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (infinite_Icc_mul_I 0 1 zero_lt_one 0)
    rintro _ ⟨s, hs, rfl⟩
    exact hroot s hs
  set T : ℝ := 1 + ∑ j, |x0 j| / y0 j with hT
  have hpos : ∀ j, 0 < x0 j + y0 j * T := by
    intro j
    have hyj : 0 < y0 j := hz j
    have h1 : |x0 j| / y0 j ≤ ∑ j, |x0 j| / y0 j :=
      Finset.single_le_sum (f := fun j => |x0 j| / y0 j)
        (fun i _ => div_nonneg (abs_nonneg _) (hz i).le) (Finset.mem_univ j)
    have h2 : y0 j * T ≥ y0 j * (1 + |x0 j| / y0 j) := by
      apply mul_le_mul_of_nonneg_left _ hyj.le; linarith
    have h3 : y0 j * (1 + |x0 j| / y0 j) = y0 j + |x0 j| := by field_simp
    linarith [neg_abs_le (x0 j)]
  have hQ := hP _ hpos
  have h2 : P.eval (T : ℂ) = 0 := by rw [hP0]; simp
  rw [eval_line] at h2
  have e3 : (fun j => (x0 j : ℂ) + (y0 j : ℂ) * (T : ℂ)) =
      fun j => ((x0 j + y0 j * T : ℝ) : ℂ) := by
    funext j; push_cast; ring
  rw [e3, aeval_ofReal] at h2
  exact hQ.ne' (by exact_mod_cast h2)

/-- A real stable polynomial satisfies `CMono`. -/
theorem mono_of_stable {Q : MvPolynomial (Fin n) ℝ} (hS : CStable Q) : CMono Q := by
  intro z v hz hv
  have key : ∀ δ : ℝ, 0 < δ →
      ‖MvPolynomial.aeval z Q‖ ≤ ‖MvPolynomial.aeval (fun j => z j + v j * I + I * δ) Q‖ := by
    intro δ hδ
    set P := line z (fun j => ((v j + δ : ℝ) : ℂ)) Q with hPdef
    have hroots : ∀ ρ ∈ P.roots, ρ.im ≤ 0 := by
      intro ρ hρ
      by_contra hpos
      have hρ' := (Polynomial.mem_roots'.1 hρ).2
      rw [IsRoot, eval_line] at hρ'
      refine hS _ (fun j => ?_) hρ'
      have : 0 < (v j + δ) * ρ.im := mul_pos (by linarith [hv j]) (not_le.1 hpos)
      simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      linarith [hz j]
    have := norm_eval_le_of_roots_im_nonpos P hroots 0 (by simp) 1 zero_le_one
    rw [eval_line, eval_line] at this
    have e1 : (fun j => z j + ((v j + δ : ℝ) : ℂ) * 0) = z := by funext j; simp
    have e2 : (fun j => z j + ((v j + δ : ℝ) : ℂ) * (0 + ((1 : ℝ) : ℂ) * I)) =
        (fun j => z j + v j * I + I * δ) := by funext j; push_cast; ring
    rwa [e1, e2] at this
  set P := line (fun j => z j + v j * I) (fun _ => I) Q with hPdef
  have hcont : Continuous (fun δ : ℝ => ‖P.eval (δ : ℂ)‖) :=
    (P.continuous.comp continuous_ofReal).norm
  have hlim : Filter.Tendsto (fun δ : ℝ => ‖P.eval (δ : ℂ)‖) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ‖P.eval ((0 : ℝ) : ℂ)‖) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : P.eval ((0 : ℝ) : ℂ) = MvPolynomial.aeval (fun j => z j + v j * I) Q := by
    rw [eval_line]; simp
  rw [h0] at hlim
  refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => ?_)
  rw [eval_line]
  exact key δ hδ

/-- Gauss–Lucas: partial derivatives of real stable polynomials are real stable, provided the
polynomial is nonconstant along every line in the direction of the variable. -/
theorem stable_pderiv {Q : MvPolynomial (Fin n) ℝ} (hS : CStable Q) (k : Fin n)
    (hdeg : ∀ z : Fin n → ℂ, 0 < (line (Function.update z k 0) (Pi.single k 1) Q).degree) :
    CStable (MvPolynomial.pderiv k Q) := by
  intro z hz h0
  set z' := Function.update z k 0 with hz'
  set h := line z' (Pi.single k 1) Q with hh
  have hdegh : 0 < h.degree := hdeg z
  have hevalh : ∀ t, h.eval t = MvPolynomial.aeval (Function.update z k t) Q := by
    intro t
    rw [hh, eval_line_single]
    simp [hz']
  have hroots : h.rootSet ℂ ⊆ {w : ℂ | w.im ≤ 0} := by
    intro ρ hρ
    rw [mem_rootSet, coe_aeval_eq_eval] at hρ
    by_contra hpos
    rw [hevalh] at hρ
    refine hS _ (fun j => ?_) hρ.2
    rcases eq_or_ne j k with rfl | hjk
    · simpa using not_le.1 hpos
    · simpa [hjk] using hz j
  have hder : z k ∈ (derivative h).rootSet ℂ := by
    rw [mem_rootSet, coe_aeval_eq_eval]
    refine ⟨?_, ?_⟩
    · intro hd
      exact (Polynomial.natDegree_pos_iff_degree_pos.2 hdegh).ne'
        (derivative_eq_zero.1 hd)
    · rw [hh, line_derivative, eval_line_single]
      simpa [hz'] using h0
  have hconv : convexHull ℝ (h.rootSet ℂ) ⊆ {w : ℂ | w.im ≤ 0} := by
    apply convexHull_min hroots
    exact convex_halfSpace_le (f := fun w : ℂ => w.im) ⟨fun _ _ => rfl, fun _ _ => by simp⟩ 0
  have := hconv (rootSet_derivative_subset_convexHull_rootSet hdegh hder)
  exact absurd (hz k) (not_lt.2 this)

lemma eval_map_conj (g : ℝ[X]) (ρ : ℂ) :
    (g.map (algebraMap ℝ ℂ)).eval ((starRingEnd ℂ) ρ) =
      (starRingEnd ℂ) ((g.map (algebraMap ℝ ℂ)).eval ρ) := by
  rw [eval_map, eval_map, Polynomial.hom_eval₂]
  congr 1
  ext a
  simp

/-- Restrictions of `CMono` polynomials to real lines in nonnegative directions are
real-rooted. -/
theorem roots_im_eq_zero_of_mono {Q : MvPolynomial (Fin n) ℝ} (hM : CMono Q) (x w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hne : ∃ t : ℝ, MvPolynomial.eval (fun j => x j + w j * t) Q ≠ 0) :
    ∀ ρ ∈ ((line x w Q).map (algebraMap ℝ ℂ)).roots, ρ.im = 0 := by
  set G := (line x w Q).map (algebraMap ℝ ℂ) with hG
  have hGne : G ≠ 0 := by
    obtain ⟨t, ht⟩ := hne
    intro h0
    have : G.eval (t : ℂ) = 0 := by rw [h0]; simp
    rw [hG, map_line, eval_line] at this
    have e : (fun j => (x j : ℂ) + (w j : ℂ) * (t : ℂ)) = fun j => ((x j + w j * t : ℝ) : ℂ) := by
      funext j; push_cast; ring
    rw [e, aeval_ofReal] at this
    exact ht (by exact_mod_cast this)
  have hup : ∀ ρ : ℂ, G.IsRoot ρ → ¬ 0 < ρ.im := by
    intro ρ hρ hpos
    apply hGne
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (infinite_Icc_mul_I 0 ρ.im hpos (ρ.re : ℂ))
    rintro _ ⟨s, hs, rfl⟩
    have hρ' := hρ
    rw [Set.mem_ofPred_eq, Polynomial.IsRoot.def]
    rw [Polynomial.IsRoot.def] at hρ'
    rw [hG, map_line, eval_line] at hρ' ⊢
    have hle := hM (fun j => ((x j + w j * ρ.re : ℝ) : ℂ) + ((w j * s : ℝ) : ℂ) * I)
      (fun j => w j * (ρ.im - s))
      (fun j => by simpa using mul_nonneg (hw j) hs.1)
      (fun j => mul_nonneg (hw j) (by linarith [hs.2]))
    have e1 : (fun j => ((x j + w j * ρ.re : ℝ) : ℂ) + ((w j * s : ℝ) : ℂ) * I +
        ((w j * (ρ.im - s) : ℝ) : ℂ) * I) = fun j => (x j : ℂ) + (w j : ℂ) * ρ := by
      funext j; apply Complex.ext <;> simp; ring
    rw [e1, hρ', norm_zero] at hle
    have e2 : (fun j => (x j : ℂ) + (w j : ℂ) * ((ρ.re : ℂ) + (s : ℂ) * I)) =
        (fun j => ((x j + w j * ρ.re : ℝ) : ℂ) + ((w j * s : ℝ) : ℂ) * I) := by
      funext j; push_cast; ring
    rw [e2]; exact norm_le_zero_iff.1 hle
  intro ρ hρ
  have hρr := (Polynomial.mem_roots'.1 hρ).2
  rcases lt_trichotomy ρ.im 0 with hneg | hzero | hpos
  · exfalso
    apply hup ((starRingEnd ℂ) ρ)
    · rw [IsRoot, hG, eval_map_conj, ← hG, hρr.eq_zero, map_zero]
    · simpa using hneg
  · exact hzero
  · exact absurd hpos (hup ρ hρr)

end VdW
