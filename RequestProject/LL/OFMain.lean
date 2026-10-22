/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LL.Chain
public import RequestProject.LL.OFExpect

/-!
# Theorem 1.2 of Linial–Luria: an upper bound on the number of 1-factorizations

`F(n)` is the number of 1-factorizations of `K_n`, viewed (as in the paper) as proper edge
colourings of `K_n` with `n - 1` colours, i.e. proper colourings of the line graph of `K_n`
with the colours `Fin (n - 1)`.  (Every such colouring partitions the edges into `n - 1`
perfect matchings; the bound below therefore also bounds the number of unordered
partitions into perfect matchings.)

* `LinialLuria.log_card_OFset_le` : the entropy argument, `log |OF(n)| ≤ n (n-1) · PsiOF n n`.
* `LinialLuria.F_le_card_OFset` : `F(n) ≤ |OF(n)|`.
* `LinialLuria.oneFactorization_upper_bound_explicit` :
  `F(n) ≤ exp ((n(n-1)/2) (log n - 2 + 1200/√(n-2)))` for `n ≥ 3`.
* `LinialLuria.theorem_1_2` : `F(n) ≤ ((1 + o(1)) n / e²)^{n²/2}`.
-/

@[expose] public section

open Finset Real

namespace LinialLuria

variable {n : ℕ}

/-- The number `F(n)` of 1-factorizations of `K_n`: proper edge colourings of the complete
graph `K_n` with the `n - 1` colours `Fin (n - 1)`. -/
noncomputable def F (n : ℕ) : ℕ :=
  Nat.card ((⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin (n - 1)))

/-- The (normalised) colourings used in the proof: proper colourings `c` with the diagonal
fixed to `k0`. -/
noncomputable def OFset (n : ℕ) (k0 : Fin (n - 1)) : Finset (Fin n → Fin n → Fin (n - 1)) := by
  classical exact univ.filter (fun c => IsOF c ∧ ∀ a, c a a = k0)

lemma mem_OFset {k0 : Fin (n - 1)} {c : Fin n → Fin n → Fin (n - 1)} :
    c ∈ OFset n k0 ↔ IsOF c ∧ ∀ a, c a a = k0 := by
  classical
  unfold OFset
  simp

/-- For every choice of the orders, the chain rule bound. -/
lemma chain_of (k0 : Fin (n - 1)) (L : ℕ) (lam nu : Fin n → Fin L) :
    ((OFset n k0).card : ℝ) * Real.log (OFset n k0).card ≤
      ∑ c ∈ OFset n k0, ∑ p ∈ offDiag (univ : Finset (Fin n)),
        Real.log (NvalOF lam nu c p.1 p.2) := by
  have h := chain_bound (ekey lam nu)
    (fun (p : Fin n × Fin n) (c : Fin n → Fin n → Fin (n - 1)) => c p.1 p.2) (offDiag univ)
    (OFset n k0) (ekey_injOn lam nu) (by
      intro c hc c' hc' h
      rw [mem_OFset] at hc hc'
      funext a b
      by_cases hab : a = b
      · subst hab; rw [hc.2, hc'.2]
      · exact h (a, b) (by simp [hab]))
  refine h.trans (sum_le_sum fun c hc => sum_le_sum fun p hp => ?_)
  rw [mem_OFset] at hc
  have hp' : p.1 ≠ p.2 := (mem_offDiag.1 hp).2.2
  have hmem : c ∈ agreeSet (OFset n k0) (offDiag univ) (ekey lam nu)
      (fun (p : Fin n × Fin n) (c : Fin n → Fin n → Fin (n - 1)) => c p.1 p.2) p c := by
    rw [mem_agreeSet, mem_OFset]; exact ⟨hc, fun _ _ _ => rfl⟩
  apply Real.log_le_log
  · exact Nat.cast_pos.2 (card_pos.2 ⟨_, mem_image_of_mem _ hmem⟩)
  · apply Nat.cast_le.2
    apply reveal_of lam nu hc.1 hp'
    intro c' hc'
    rw [mem_agreeSet, mem_OFset] at hc'
    exact ⟨hc'.1.1, fun a b hab hk => hc'.2 (a, b) (by simp [hab]) hk⟩

lemma PsiOF_nonneg (L : ℕ) (hn : 2 ≤ n) : 0 ≤ PsiOF L n := by
  unfold PsiOF
  apply sum_nonneg
  intro r _
  apply mul_nonneg (by positivity)
  apply wsum_nonneg
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : 0 ≤ (n : ℝ) - 2 := by linarith
  positivity

/-- **The entropy bound**: `log |OF(n)| ≤ n (n - 1) · PsiOF n n`. -/
theorem log_card_OFset_le (hn : 3 ≤ n) (k0 : Fin (n - 1)) :
    Real.log (OFset n k0).card ≤ (n * (n - 1) : ℝ) * PsiOF n n := by
  have hL : 1 ≤ n := by omega
  have hPsi := PsiOF_nonneg n (show 2 ≤ n by omega)
  have hn1 : (0 : ℝ) ≤ n * (n - 1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith
  rcases Nat.eq_zero_or_pos (OFset n k0).card with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; positivity
  set S := OFset n k0 with hS
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hpos
  have hsum : ∑ lam : Fin n → Fin n, ∑ nu : Fin n → Fin n,
      ((S.card : ℝ) * Real.log S.card) ≤
      ∑ lam : Fin n → Fin n, ∑ nu : Fin n → Fin n, ∑ c ∈ S,
        ∑ p ∈ offDiag (univ : Finset (Fin n)), Real.log (NvalOF lam nu c p.1 p.2) :=
    sum_le_sum fun lam _ => sum_le_sum fun nu _ => chain_of k0 n lam nu
  have hswap : ∑ lam : Fin n → Fin n, ∑ nu : Fin n → Fin n, ∑ c ∈ S,
      ∑ p ∈ offDiag (univ : Finset (Fin n)), Real.log (NvalOF lam nu c p.1 p.2) =
      ∑ c ∈ S, ∑ p ∈ offDiag (univ : Finset (Fin n)), ∑ lam : Fin n → Fin n,
        ∑ nu : Fin n → Fin n, Real.log (NvalOF lam nu c p.1 p.2) := by
    have e1 : ∀ lam : Fin n → Fin n, ∑ nu : Fin n → Fin n, ∑ c ∈ S,
        ∑ p ∈ offDiag (univ : Finset (Fin n)), Real.log (NvalOF lam nu c p.1 p.2) =
        ∑ c ∈ S, ∑ p ∈ offDiag (univ : Finset (Fin n)), ∑ nu : Fin n → Fin n,
          Real.log (NvalOF lam nu c p.1 p.2) := by
      intro lam
      rw [sum_comm]
      apply sum_congr rfl; intro c _
      rw [sum_comm]
    rw [sum_congr rfl (fun lam _ => e1 lam), sum_comm]
    apply sum_congr rfl; intro c _
    rw [sum_comm]
  rw [hswap] at hsum
  have hexp : ∑ c ∈ S, ∑ p ∈ offDiag (univ : Finset (Fin n)), ∑ lam : Fin n → Fin n,
      ∑ nu : Fin n → Fin n, Real.log (NvalOF lam nu c p.1 p.2) ≤
      ∑ c ∈ S, ∑ p ∈ offDiag (univ : Finset (Fin n)), ((n : ℝ) ^ n) ^ 2 * PsiOF n n := by
    apply sum_le_sum; intro c hc
    apply sum_le_sum; intro p hp
    rw [hS, mem_OFset] at hc
    exact expect_of hc.1 (mem_offDiag.1 hp).2.2 hL
  have hcard : (offDiag (univ : Finset (Fin n))).card = n * n - n := by
    rw [offDiag_card, card_univ, Fintype.card_fin]
  have hcardR : ((offDiag (univ : Finset (Fin n))).card : ℝ) = n * (n - 1) := by
    rw [hcard, Nat.cast_sub (Nat.le_mul_self n)]; push_cast; ring
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    hcardR] at hsum hexp
  have hfin := hsum.trans hexp
  have hLn : (0 : ℝ) < (n : ℝ) ^ n := by
    have : (0 : ℝ) < n := by exact_mod_cast hL
    positivity
  push_cast at hfin
  have key : ((n : ℝ) ^ n) ^ 2 * (S.card * Real.log S.card) ≤
      ((n : ℝ) ^ n) ^ 2 * (S.card * ((n * (n - 1) : ℝ) * PsiOF n n)) := by
    nlinarith
  have key2 := le_of_mul_le_mul_left key (by positivity)
  exact le_of_mul_le_mul_left (by linarith) hSpos

/-! ### From colourings of the line graph to normalised colourings -/

/-- The colour matrix of a proper edge colouring (with diagonal `k0`). -/
noncomputable def colMatrix (k0 : Fin (n - 1))
    (C : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin (n - 1))) :
    Fin n → Fin n → Fin (n - 1) := fun a b =>
  if h : a ≠ b then C ⟨s(a, b), (SimpleGraph.mem_edgeSet _).2 ((SimpleGraph.top_adj a b).2 h)⟩
  else k0

lemma colMatrix_mem (k0 : Fin (n - 1))
    (C : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin (n - 1))) :
    colMatrix k0 C ∈ OFset n k0 := by
  rw [mem_OFset]
  refine ⟨⟨fun a b => ?_, fun a b b' hb hb' h => ?_⟩, fun a => ?_⟩
  · unfold colMatrix
    by_cases hab : a = b
    · subst hab; rfl
    · rw [dif_pos (Ne.symm hab), dif_pos hab]
      congr 2
      exact Sym2.eq_swap
  · by_contra hbb
    unfold colMatrix at h
    rw [dif_pos hb, dif_pos hb'] at h
    refine C.valid ?_ h
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨?_, a, by simp, by simp⟩
    intro he
    simp only [Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at he
    rcases he with ⟨-, h1⟩ | ⟨h1, h2⟩
    · exact hbb h1
    · exact hb h2.symm
  · unfold colMatrix
    rw [dif_neg (not_not.2 rfl)]

lemma colMatrix_injective (k0 : Fin (n - 1)) : Function.Injective (colMatrix (n := n) k0) := by
  intro C C' h
  apply RelHom.ext
  rintro ⟨z, hz⟩
  induction z using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := (SimpleGraph.top_adj a b).1 ((SimpleGraph.mem_edgeSet _).1 hz)
    have := congrFun (congrFun h a) b
    unfold colMatrix at this
    rw [dif_pos hab, dif_pos hab] at this
    exact this

/-- `F(n) ≤ |OF(n)|`. -/
theorem F_le_card_OFset (k0 : Fin (n - 1)) : F n ≤ (OFset n k0).card := by
  classical
  unfold F
  have hinj : Function.Injective (fun C : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring
      (Fin (n - 1)) => (⟨colMatrix k0 C, colMatrix_mem k0 C⟩ : OFset n k0)) := by
    intro C C' h
    simp only [Subtype.mk.injEq] at h
    exact colMatrix_injective k0 h
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

/-! ### The main theorems -/

/-- **Theorem 1.2, explicit form**: for `n ≥ 3`,
`F(n) ≤ exp ((n (n-1) / 2) · (log n - 2 + 1200 / √(n-2)))`. -/
theorem oneFactorization_upper_bound_explicit (n : ℕ) (hn : 3 ≤ n) :
    (F n : ℝ) ≤
      Real.exp ((n * (n - 1) / 2 : ℝ) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 2))) := by
  set k0 : Fin (n - 1) := ⟨0, by omega⟩
  have h1 := log_card_OFset_le hn k0
  have h2 := PsiOF_asymp n hn
  have hn1 : (0 : ℝ) ≤ n * (n - 1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith
  have h3 : Real.log (OFset n k0).card ≤
      (n * (n - 1) / 2 : ℝ) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 2)) := by
    calc Real.log (OFset n k0).card ≤ (n * (n - 1) : ℝ) * PsiOF n n := h1
      _ ≤ (n * (n - 1) : ℝ) * ((1 / 2) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 2))) :=
          mul_le_mul_of_nonneg_left h2 hn1
      _ = _ := by ring
  have hF : (F n : ℝ) ≤ (OFset n k0).card := by exact_mod_cast F_le_card_OFset k0
  rcases Nat.eq_zero_or_pos (OFset n k0).card with h0 | hpos
  · rw [h0] at hF; simp only [Nat.cast_zero] at hF
    exact hF.trans (Real.exp_pos _).le
  have hpos' : (0 : ℝ) < (OFset n k0).card := by exact_mod_cast hpos
  calc (F n : ℝ) ≤ (OFset n k0).card := hF
    _ = Real.exp (Real.log (OFset n k0).card) := (Real.exp_log hpos').symm
    _ ≤ _ := Real.exp_le_exp.2 h3

/-- **Theorem 1.2** (Linial–Luria): `F(n) ≤ ((1 + o(1)) n / e²)^{n²/2}`; that is, for every
`ε > 0` and all sufficiently large `n`, `F(n) ≤ ((1 + ε) n / e²)^{n²/2}`. -/
theorem theorem_1_2 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (F n : ℝ) ≤ ((1 + ε) * n / Real.exp 2) ^ ((n : ℝ) ^ 2 / 2) := by
  have hlog : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  set K : ℝ := (1200 / Real.log (1 + ε)) ^ 2 + 2 with hK
  obtain ⟨N, hN⟩ := exists_nat_ge (max K 8)
  rw [Filter.eventually_atTop]
  refine ⟨max N 8, fun n hn => ?_⟩
  have hn8 : 8 ≤ n := le_of_max_le_right hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hnK : K ≤ n := (le_of_max_le_left hN).trans hnN
  have hnr : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hlogn : 2 ≤ Real.log n := by
    have h2 : Real.exp 2 ≤ n := by
      have : Real.exp 2 < 7.4 := by
        have := Real.exp_one_lt_d9
        have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e2]; nlinarith [Real.exp_pos 1]
      linarith
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) h2
  have herr : 1200 / Real.sqrt ((n : ℝ) - 2) ≤ Real.log (1 + ε) := by
    have hsq : 1200 / Real.log (1 + ε) ≤ Real.sqrt ((n : ℝ) - 2) := by
      rw [Real.le_sqrt (by positivity) (by linarith)]
      linarith
    have hs0 : 0 < Real.sqrt ((n : ℝ) - 2) := Real.sqrt_pos.2 (by linarith)
    rw [div_le_iff₀ hs0]
    rw [div_le_iff₀ hlog] at hsq
    linarith
  have hexp := oneFactorization_upper_bound_explicit n (by omega)
  have hpos : (0 : ℝ) < (1 + ε) * n / Real.exp 2 := by positivity
  have hbr : 0 ≤ Real.log n - 2 + Real.log (1 + ε) := by linarith
  have hmain : (n * (n - 1) / 2 : ℝ) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 2)) ≤
      ((n : ℝ) ^ 2 / 2) * Real.log ((1 + ε) * n / Real.exp 2) := by
    rw [Real.log_div (by positivity) (Real.exp_pos 2).ne', Real.log_mul (by linarith)
      (by positivity), Real.log_exp]
    have h1 : (n * (n - 1) / 2 : ℝ) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 2)) ≤
        (n * (n - 1) / 2 : ℝ) * (Real.log n - 2 + Real.log (1 + ε)) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      have : (0 : ℝ) ≤ n * (n - 1) := by nlinarith
      positivity
    have h2 : (n * (n - 1) / 2 : ℝ) * (Real.log n - 2 + Real.log (1 + ε)) ≤
        ((n : ℝ) ^ 2 / 2) * (Real.log n - 2 + Real.log (1 + ε)) := by
      apply mul_le_mul_of_nonneg_right _ hbr
      nlinarith
    linarith
  calc (F n : ℝ) ≤ _ := hexp
    _ ≤ Real.exp (((n : ℝ) ^ 2 / 2) * Real.log ((1 + ε) * n / Real.exp 2)) :=
        Real.exp_le_exp.2 hmain
    _ = _ := by
        rw [Real.rpow_def_of_pos hpos, mul_comm]

end LinialLuria
