/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Defs
public import RequestProject.LL.Chain
public import RequestProject.LL.STSExpect

/-!
# Theorem 1.1 of Linial–Luria: an upper bound on the number of Steiner triple systems

`STS(n)`, the number of Steiner triple systems on the vertex set `Fin n`, is `STS.D n`
(defined in `RequestProject/Defs.lean`).

* `LinialLuria.log_card_SQset_le` : the entropy (chain rule) argument,
  `log |SQ(n)| ≤ n (n-1) · PsiSTS n n`.
* `LinialLuria.D_le_card_SQset` : `STS(n) ≤ |SQ(n)|`.
* `LinialLuria.sts_upper_bound_explicit` :
  `STS(n) ≤ exp ((n(n-1)/6) (log n - 2 + 1200/√(n-3)))` for `n ≥ 4`.
* `LinialLuria.theorem_1_1` : `STS(n) ≤ ((1 + o(1)) n / e²)^{n²/6}`.
-/

@[expose] public section

open Finset Real

namespace LinialLuria

variable {n : ℕ}

/-- The Steiner quasigroups on `Fin n`. -/
noncomputable def SQset (n : ℕ) : Finset (Fin n → Fin n → Fin n) := by
  classical exact univ.filter IsSQ

lemma mem_SQset {T : Fin n → Fin n → Fin n} : T ∈ SQset n ↔ IsSQ T := by
  classical
  unfold SQset
  simp

/-! ### The entropy argument -/

/-- For every choice of the orders, the chain rule bound. -/
lemma chain_sts (L : ℕ) (lam nu : Fin n → Fin L) :
    ((SQset n).card : ℝ) * Real.log (SQset n).card ≤
      ∑ T ∈ SQset n, ∑ p ∈ offDiag (univ : Finset (Fin n)),
        Real.log (NvalSTS lam nu T p.1 p.2) := by
  have h := chain_bound (ekey lam nu) (fun (p : Fin n × Fin n) (T : Fin n → Fin n → Fin n) =>
    T p.1 p.2) (offDiag univ) (SQset n) (ekey_injOn lam nu) (by
      intro T hT T' hT' h
      rw [mem_SQset] at hT hT'
      funext a b
      by_cases hab : a = b
      · subst hab; rw [hT.diag, hT'.diag]
      · exact h (a, b) (by simp [hab]))
  refine h.trans (sum_le_sum fun T hT => sum_le_sum fun p hp => ?_)
  rw [mem_SQset] at hT
  have hp' : p.1 ≠ p.2 := (mem_offDiag.1 hp).2.2
  have hmem : T ∈ agreeSet (SQset n) (offDiag univ) (ekey lam nu)
      (fun (p : Fin n × Fin n) (T : Fin n → Fin n → Fin n) => T p.1 p.2) p T := by
    rw [mem_agreeSet, mem_SQset]; exact ⟨hT, fun _ _ _ => rfl⟩
  apply Real.log_le_log
  · exact Nat.cast_pos.2 (card_pos.2 ⟨_, mem_image_of_mem _ hmem⟩)
  · apply Nat.cast_le.2
    apply reveal_sts lam nu hT hp'
    intro T' hT'
    rw [mem_agreeSet, mem_SQset] at hT'
    exact ⟨hT'.1, fun a b hab hk => hT'.2 (a, b) (by simp [hab]) hk⟩

lemma PsiSTS_nonneg (L : ℕ) (hn : 3 ≤ n) : 0 ≤ PsiSTS L n := by
  unfold PsiSTS
  apply sum_nonneg
  intro r _
  apply mul_nonneg (by positivity)
  apply wsum_nonneg
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have : 0 ≤ (n : ℝ) - 3 := by linarith
  positivity

/-- **The entropy bound**: `log |SQ(n)| ≤ n (n - 1) · PsiSTS n n`. -/
theorem log_card_SQset_le (hn : 4 ≤ n) :
    Real.log (SQset n).card ≤ (n * (n - 1) : ℝ) * PsiSTS n n := by
  set L := n with hLdef
  have hL : 1 ≤ L := by omega
  have hPsi := PsiSTS_nonneg L (show 3 ≤ n by omega)
  have hn1 : (0 : ℝ) ≤ n * (n - 1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith
  rcases Nat.eq_zero_or_pos (SQset n).card with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; positivity
  set S := SQset n with hS
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hpos
  -- sum the chain bound over all orders
  have hsum : ∑ lam : Fin n → Fin L, ∑ nu : Fin n → Fin L,
      ((S.card : ℝ) * Real.log S.card) ≤
      ∑ lam : Fin n → Fin L, ∑ nu : Fin n → Fin L, ∑ T ∈ S,
        ∑ p ∈ offDiag (univ : Finset (Fin n)), Real.log (NvalSTS lam nu T p.1 p.2) :=
    sum_le_sum fun lam _ => sum_le_sum fun nu _ => chain_sts L lam nu
  have hswap : ∑ lam : Fin n → Fin L, ∑ nu : Fin n → Fin L, ∑ T ∈ S,
      ∑ p ∈ offDiag (univ : Finset (Fin n)), Real.log (NvalSTS lam nu T p.1 p.2) =
      ∑ T ∈ S, ∑ p ∈ offDiag (univ : Finset (Fin n)), ∑ lam : Fin n → Fin L,
        ∑ nu : Fin n → Fin L, Real.log (NvalSTS lam nu T p.1 p.2) := by
    have e1 : ∀ lam : Fin n → Fin L, ∑ nu : Fin n → Fin L, ∑ T ∈ S,
        ∑ p ∈ offDiag (univ : Finset (Fin n)), Real.log (NvalSTS lam nu T p.1 p.2) =
        ∑ T ∈ S, ∑ p ∈ offDiag (univ : Finset (Fin n)), ∑ nu : Fin n → Fin L,
          Real.log (NvalSTS lam nu T p.1 p.2) := by
      intro lam
      rw [sum_comm]
      apply sum_congr rfl; intro T _
      rw [sum_comm]
    rw [sum_congr rfl (fun lam _ => e1 lam), sum_comm]
    apply sum_congr rfl; intro T _
    rw [sum_comm]
  rw [hswap] at hsum
  have hexp : ∑ T ∈ S, ∑ p ∈ offDiag (univ : Finset (Fin n)), ∑ lam : Fin n → Fin L,
      ∑ nu : Fin n → Fin L, Real.log (NvalSTS lam nu T p.1 p.2) ≤
      ∑ T ∈ S, ∑ p ∈ offDiag (univ : Finset (Fin n)), ((L : ℝ) ^ n) ^ 2 * PsiSTS L n := by
    apply sum_le_sum; intro T hT
    apply sum_le_sum; intro p hp
    rw [hS, mem_SQset] at hT
    exact expect_sts hT (mem_offDiag.1 hp).2.2 hL
  have hcard : (offDiag (univ : Finset (Fin n))).card = n * n - n := by
    rw [offDiag_card, card_univ, Fintype.card_fin]
  have hcardR : ((offDiag (univ : Finset (Fin n))).card : ℝ) = n * (n - 1) := by
    rw [hcard, Nat.cast_sub (Nat.le_mul_self n)]; push_cast; ring
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    hcardR] at hsum hexp
  have hfin := hsum.trans hexp
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  push_cast at hfin
  have key : ((L : ℝ) ^ n) ^ 2 * (S.card * Real.log S.card) ≤
      ((L : ℝ) ^ n) ^ 2 * (S.card * ((n * (n - 1) : ℝ) * PsiSTS L n)) := by
    nlinarith
  have key2 := le_of_mul_le_mul_left key (by positivity)
  exact le_of_mul_le_mul_left (by linarith) hSpos

/-! ### From Steiner triple systems to Steiner quasigroups -/

section Third

variable {B : Finset (Finset (Fin n))}

lemma exists_third (hB : STS.IsSTS B) {a b : Fin n} (hab : a ≠ b) :
    ∃ c, c ≠ a ∧ c ≠ b ∧ ({a, b, c} : Finset (Fin n)) ∈ B := by
  obtain ⟨A, ⟨hA, haA, hbA⟩, -⟩ := hB.2 a b hab
  have h3 := hB.1 A hA
  have hcard : ((A.erase a).erase b).card = 1 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨Ne.symm hab, hbA⟩), card_erase_of_mem haA, h3]
  obtain ⟨c, hc⟩ := card_eq_one.1 hcard
  have hcm : c ∈ (A.erase a).erase b := by rw [hc]; exact mem_singleton_self c
  simp only [mem_erase] at hcm
  refine ⟨c, hcm.2.1, hcm.1, ?_⟩
  have : A = {a, b, c} := by
    ext x
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      by_cases hxb : x = b
      · exact Or.inr (Or.inl hxb)
      have : x ∈ (A.erase a).erase b := by simp [hxa, hxb, hx]
      rw [hc, mem_singleton] at this
      exact Or.inr (Or.inr this)
    · rintro (rfl | rfl | rfl)
      · exact haA
      · exact hbA
      · exact hcm.2.2
  rw [← this]; exact hA

lemma third_unique (hB : STS.IsSTS B) {a b c c' : Fin n} (hab : a ≠ b)
    (hc : ({a, b, c} : Finset (Fin n)) ∈ B)
    (hc'a : c' ≠ a) (hc'b : c' ≠ b) (hc' : ({a, b, c'} : Finset (Fin n)) ∈ B) : c = c' := by
  obtain ⟨A, -, hAu⟩ := hB.2 a b hab
  have e1 := hAu {a, b, c} ⟨hc, by simp, by simp⟩
  have e2 := hAu {a, b, c'} ⟨hc', by simp, by simp⟩
  have : c' ∈ ({a, b, c} : Finset (Fin n)) := by rw [e1, ← e2]; simp
  simp only [mem_insert, mem_singleton] at this
  rcases this with h | h | h
  · exact absurd h hc'a
  · exact absurd h hc'b
  · exact h.symm

/-- The third point of the block through `a` and `b` (and `a` if `a = b`). -/
noncomputable def thirdPt (B : Finset (Finset (Fin n))) (a b : Fin n) : Fin n := by
  classical
  exact if h : a ≠ b ∧ ∃ c, c ≠ a ∧ c ≠ b ∧ ({a, b, c} : Finset (Fin n)) ∈ B then
    Classical.choose h.2 else a

lemma thirdPt_spec (hB : STS.IsSTS B) {a b : Fin n} (hab : a ≠ b) :
    thirdPt B a b ≠ a ∧ thirdPt B a b ≠ b ∧
      ({a, b, thirdPt B a b} : Finset (Fin n)) ∈ B := by
  classical
  have h : a ≠ b ∧ ∃ c, c ≠ a ∧ c ≠ b ∧ ({a, b, c} : Finset (Fin n)) ∈ B :=
    ⟨hab, exists_third hB hab⟩
  unfold thirdPt
  rw [dif_pos h]
  exact Classical.choose_spec h.2

lemma thirdPt_eq (hB : STS.IsSTS B) {a b c : Fin n} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hc : ({a, b, c} : Finset (Fin n)) ∈ B) : thirdPt B a b = c := by
  obtain ⟨h1, h2, h3⟩ := thirdPt_spec hB hab
  exact third_unique hB hab h3 hca hcb hc

lemma thirdPt_isSQ (hB : STS.IsSTS B) : IsSQ (thirdPt B) := by
  classical
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · unfold thirdPt; rw [dif_neg]; simp
  obtain ⟨h1, h2, h3⟩ := thirdPt_spec hB hab
  refine ⟨h1, h2, ?_, ?_⟩
  · apply thirdPt_eq hB (Ne.symm hab) h2 h1
    have : ({b, a, thirdPt B a b} : Finset (Fin n)) = {a, b, thirdPt B a b} := by
      ext; simp; tauto
    rw [this]; exact h3
  · apply thirdPt_eq hB (Ne.symm h1) (Ne.symm hab) (Ne.symm h2)
    have : ({a, thirdPt B a b, b} : Finset (Fin n)) = {a, b, thirdPt B a b} := by
      ext; simp; tauto
    rw [this]; exact h3

lemma mem_of_thirdPt (hB : STS.IsSTS B) {A : Finset (Fin n)} (hA : A ∈ B) :
    ∃ a b, a ≠ b ∧ A = {a, b, thirdPt B a b} := by
  have h3 := hB.1 A hA
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.1 h3
  refine ⟨a, b, hab, ?_⟩
  rw [thirdPt_eq hB hab (Ne.symm hac) (Ne.symm hbc) hA]

end Third

lemma thirdPt_injective {B B' : Finset (Finset (Fin n))} (hB : STS.IsSTS B)
    (hB' : STS.IsSTS B') (h : thirdPt B = thirdPt B') : B = B' := by
  have sub : ∀ {B B' : Finset (Finset (Fin n))}, STS.IsSTS B → STS.IsSTS B' →
      thirdPt B = thirdPt B' → B ⊆ B' := by
    intro B B' hB hB' h A hA
    obtain ⟨a, b, hab, rfl⟩ := mem_of_thirdPt hB hA
    rw [h]
    exact (thirdPt_spec hB' hab).2.2
  exact Subset.antisymm (sub hB hB' h) (sub hB' hB h.symm)

/-- `STS(n) ≤ |SQ(n)|`. -/
theorem D_le_card_SQset (n : ℕ) : STS.D n ≤ (SQset n).card := by
  classical
  unfold STS.D
  have hinj : Function.Injective (fun B : STS.STSOn n =>
      (⟨thirdPt B.1, mem_SQset.2 (thirdPt_isSQ B.2)⟩ : SQset n)) := by
    intro B B' h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (thirdPt_injective B.2 B'.2 h)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

/-! ### The main theorems -/

/-- **Theorem 1.1, explicit form**: for `n ≥ 4`,
`STS(n) ≤ exp ((n (n-1) / 6) · (log n - 2 + 1200 / √(n-3)))`. -/
theorem sts_upper_bound_explicit (n : ℕ) (hn : 4 ≤ n) :
    (STS.D n : ℝ) ≤
      Real.exp ((n * (n - 1) / 6 : ℝ) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 3))) := by
  have h1 := log_card_SQset_le hn
  have h2 := PsiSTS_asymp n hn
  have hn1 : (0 : ℝ) ≤ n * (n - 1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith
  have h3 : Real.log (SQset n).card ≤
      (n * (n - 1) / 6 : ℝ) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 3)) := by
    calc Real.log (SQset n).card ≤ (n * (n - 1) : ℝ) * PsiSTS n n := h1
      _ ≤ (n * (n - 1) : ℝ) * ((1 / 6) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 3))) :=
          mul_le_mul_of_nonneg_left h2 hn1
      _ = _ := by ring
  have hD : (STS.D n : ℝ) ≤ (SQset n).card := by exact_mod_cast D_le_card_SQset n
  rcases Nat.eq_zero_or_pos (SQset n).card with h0 | hpos
  · rw [h0] at hD; simp only [Nat.cast_zero] at hD
    exact hD.trans (Real.exp_pos _).le
  have hpos' : (0 : ℝ) < (SQset n).card := by exact_mod_cast hpos
  calc (STS.D n : ℝ) ≤ (SQset n).card := hD
    _ = Real.exp (Real.log (SQset n).card) := (Real.exp_log hpos').symm
    _ ≤ _ := Real.exp_le_exp.2 h3

/-- **Theorem 1.1** (Linial–Luria): `STS(n) ≤ ((1 + o(1)) n / e²)^{n²/6}`; that is, for every
`ε > 0` and all sufficiently large `n`, `STS(n) ≤ ((1 + ε) n / e²)^{n²/6}`. -/
theorem theorem_1_1 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (STS.D n : ℝ) ≤ ((1 + ε) * n / Real.exp 2) ^ ((n : ℝ) ^ 2 / 6) := by
  have hlog : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  set K : ℝ := (1200 / Real.log (1 + ε)) ^ 2 + 3 with hK
  obtain ⟨N, hN⟩ := exists_nat_ge (max K 8)
  rw [Filter.eventually_atTop]
  refine ⟨max N 8, fun n hn => ?_⟩
  have hn8 : 8 ≤ n := le_of_max_le_right hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hnK : K ≤ n := (le_of_max_le_left hN).trans hnN
  have hnr : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hlogn : 2 ≤ Real.log n := by
    have h := Real.add_one_le_exp 2
    have h2 : Real.exp 2 ≤ n := by
      have : Real.exp 2 < 7.4 := by
        have := Real.exp_one_lt_d9
        have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [e2]; nlinarith [Real.exp_pos 1]
      linarith
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) h2
  -- the error term is at most `log (1 + ε)`
  have herr : 1200 / Real.sqrt ((n : ℝ) - 3) ≤ Real.log (1 + ε) := by
    have hsq : 1200 / Real.log (1 + ε) ≤ Real.sqrt ((n : ℝ) - 3) := by
      rw [Real.le_sqrt (by positivity) (by linarith)]
      linarith
    have hs0 : 0 < Real.sqrt ((n : ℝ) - 3) := Real.sqrt_pos.2 (by linarith)
    rw [div_le_iff₀ hs0]
    rw [div_le_iff₀ hlog] at hsq
    linarith
  have hexp := sts_upper_bound_explicit n (by omega)
  have hpos : (0 : ℝ) < (1 + ε) * n / Real.exp 2 := by positivity
  have hbr : 0 ≤ Real.log n - 2 + Real.log (1 + ε) := by linarith
  have hmain : (n * (n - 1) / 6 : ℝ) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 3)) ≤
      ((n : ℝ) ^ 2 / 6) * Real.log ((1 + ε) * n / Real.exp 2) := by
    rw [Real.log_div (by positivity) (Real.exp_pos 2).ne', Real.log_mul (by linarith)
      (by positivity), Real.log_exp]
    have h1 : (n * (n - 1) / 6 : ℝ) * (Real.log n - 2 + 1200 / Real.sqrt ((n : ℝ) - 3)) ≤
        (n * (n - 1) / 6 : ℝ) * (Real.log n - 2 + Real.log (1 + ε)) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      have : (0 : ℝ) ≤ n * (n - 1) := by nlinarith
      positivity
    have h2 : (n * (n - 1) / 6 : ℝ) * (Real.log n - 2 + Real.log (1 + ε)) ≤
        ((n : ℝ) ^ 2 / 6) * (Real.log n - 2 + Real.log (1 + ε)) := by
      apply mul_le_mul_of_nonneg_right _ hbr
      nlinarith
    linarith
  calc (STS.D n : ℝ) ≤ _ := hexp
    _ ≤ Real.exp (((n : ℝ) ^ 2 / 6) * Real.log ((1 + ε) * n / Real.exp 2)) :=
        Real.exp_le_exp.2 hmain
    _ = _ := by
        rw [Real.rpow_def_of_pos hpos, mul_comm]

end LinialLuria
