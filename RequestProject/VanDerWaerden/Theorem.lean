/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Defs
public import RequestProject.VanDerWaerden.Gurvits

/-!
# The van der Waerden permanent theorem

`STS.van_der_waerden` : the permanent of every doubly stochastic `n × n` real matrix is at least
`n!/n^n` (Egorychev 1981, Falikman 1981). The proof follows Gurvits, as simplified by Laurent and
Schrijver: the case of positive matrices is `VdW.permanent_ge_of_pos`, and the general case follows
by approximating a doubly stochastic matrix `M` by the positive doubly stochastic matrices
`(1 - ε) M + ε J`, `J = (1/n)`, and continuity of the permanent.
-/

@[expose] public section

open Finset Filter Topology

namespace VdW

/-- The perturbation `(1 - ε) M + ε J` of a matrix `M`, where `J` has all entries `1/n`. -/
noncomputable def perturb {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (1 - ε) * M i j + ε / n

lemma perturb_mem {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M ∈ doublyStochastic ℝ (Fin n))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : perturb M ε ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum] at hM ⊢
  obtain ⟨hnn, hrow, hcol⟩ := hM
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · simp only [perturb, Matrix.of_apply]
    have := hnn i j
    have : (0 : ℝ) ≤ 1 - ε := by linarith
    positivity
  · have hn : (n : ℝ) ≠ 0 := by
      have := i.pos; positivity
    simp only [perturb, Matrix.of_apply, sum_add_distrib, ← mul_sum, hrow i, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · have hn : (n : ℝ) ≠ 0 := by
      have := j.pos; positivity
    simp only [perturb, Matrix.of_apply, sum_add_distrib, ← mul_sum, hcol j, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

lemma perturb_pos {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M ∈ doublyStochastic ℝ (Fin n))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (i j : Fin n) : 0 < perturb M ε i j := by
  simp only [perturb, Matrix.of_apply]
  have h1 := nonneg_of_mem_doublyStochastic hM (i := i) (j := j)
  have h2 : (0 : ℝ) ≤ 1 - ε := by linarith
  have h3 : (0 : ℝ) < n := by exact_mod_cast i.pos
  have : 0 < ε / n := div_pos hε0 h3
  nlinarith [mul_nonneg h2 h1]

lemma continuous_permanent_perturb {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun ε : ℝ => (perturb M ε).permanent := by
  simp only [Matrix.permanent, perturb, Matrix.of_apply]
  fun_prop

end VdW

namespace STS

/-- **The van der Waerden permanent theorem** (Egorychev 1981, Falikman 1981): the permanent of a
doubly stochastic `n × n` matrix is at least `n!/n^n`. -/
theorem van_der_waerden : vdWPC := by
  intro n M hM
  have hlim : Tendsto (fun ε : ℝ => (VdW.perturb M ε).permanent) (𝓝[>] 0)
      (𝓝 (VdW.perturb M 0).permanent) :=
    ((VdW.continuous_permanent_perturb M).tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : VdW.perturb M 0 = M := by
    ext i j; simp [VdW.perturb]
  rw [h0] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  exact VdW.permanent_ge_of_pos _ (VdW.perturb_mem hM hε.1.le hε.2.le)
    (VdW.perturb_pos hM hε.1 hε.2.le)

end STS
