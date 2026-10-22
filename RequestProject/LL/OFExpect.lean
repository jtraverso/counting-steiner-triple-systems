/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LL.OFReveal
public import RequestProject.LL.Expect
public import RequestProject.LL.Estimates

/-!
# The expectation of `log N_{i,j}` (1-factorizations)

As for Steiner triple systems (`RequestProject/LL/STSExpect.lean`):

* `stepA_of` : the average over the edge order (conditioning on the position of `j` in the
  star of `i`; given `M_{i,j} = m`, `N_{i,j}` is essentially uniform on `{1, …, m}`);
* `stepB_of` : the average over the vertex order (Lemmas 2.1 and 2.2 of the paper);
* `expect_of` : `∑_{λ, ν} log N_{i,j} ≤ L^{2n} · PsiOF L n`.
-/

@[expose] public section

open Finset

namespace LinialLuria

variable {n L : ℕ}

/-- The vertices `a ∉ {i, j}` with `i ≪ a` whose colour `X_{i,a}` is not used on an edge
`{t, j}` with `t ≪ i` (these colours form the set `M_{i,j} ∖ {X_{i,j}}` of the paper). -/
def Mset1 (lam : Fin n → Fin L) (c : Fin n → Fin n → Fin (n - 1)) (i j : Fin n) :
    Finset (Fin n) :=
  univ.filter (fun a => a ≠ i ∧ a ≠ j ∧ vpos lam i < vpos lam a ∧
    ∀ t, vpos lam t < vpos lam i → c t j ≠ c i a)

lemma NvalOF_eq (lam nu : Fin n → Fin L) (c : Fin n → Fin n → Fin (n - 1)) (i j : Fin n)
    (h : vpos lam i < vpos lam j) :
    NvalOF lam nu c i j = 1 + ((Mset1 lam c i j).filter (fun a => vpos nu j < vpos nu a)).card := by
  unfold NvalOF Mset1
  rw [if_pos h, filter_filter]
  congr 2
  ext a
  simp only [mem_filter, mem_univ, true_and]
  tauto

lemma NvalOF_of_not (lam nu : Fin n → Fin L) (c : Fin n → Fin n → Fin (n - 1)) (i j : Fin n)
    (h : ¬ vpos lam i < vpos lam j) : NvalOF lam nu c i j = 1 := by
  unfold NvalOF
  rw [if_neg h]

/-- **Step A**: the average over the edge order. -/
theorem stepA_of {i j : Fin n} (c : Fin n → Fin n → Fin (n - 1))
    (lam : Fin n → Fin L) (hL : 1 ≤ L) (hc : vpos lam i < vpos lam j) :
    ∑ nu : Fin n → Fin L, Real.log (NvalOF lam nu c i j) ≤
      (L : ℝ) ^ n * wsum 1 L (Mset1 lam c i j).card := by
  set M := Mset1 lam c i j with hM
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set C : (Fin n → Fin L) → ℕ := fun nu => (M.filter (fun a => vpos nu j < vpos nu a)).card
    with hC
  rw [sum_split_value j]
  have per_z : ∀ z : Fin L, ∑ nu ∈ univ.filter (fun nu : Fin n → Fin L => nu j = z),
      Real.log (NvalOF lam nu c i j) ≤
      (L : ℝ) ^ n * (1 / (L : ℝ) * Real.log (1 + M.card * (((L : ℝ) - (z : ℕ)) / L))) := by
    intro z
    set B := boxF (insert j (∅ : Finset (Fin n))) (Abox z j) with hBdef
    have hB : ∑ nu ∈ univ.filter (fun nu : Fin n → Fin L => nu j = z),
        Real.log (NvalOF lam nu c i j) = ∑ nu ∈ B, Real.log (1 + 1 * (C nu : ℝ)) := by
      apply sum_congr
      · ext nu
        rw [hBdef, mem_boxF_Abox z j ∅ (notMem_empty j)]
        simp
      · intro nu _
        rw [NvalOF_eq lam nu c i j hc]
        simp only [hC, hM]; push_cast; ring_nf
    rw [hB]
    have hqB : (B.card : ℝ) ≤ (L : ℝ) ^ n * (1 / (L : ℝ)) := by
      have h := boxF_card_le (insert j (∅ : Finset (Fin n))) (Abox z j) (fun _ => 1)
        (fun v hv => by
          simp only [mem_insert, notMem_empty, or_false] at hv
          have := card_Abox_le z j v
          rwa [if_pos hv] at this)
      rw [prod_const_one, card_insert_of_notMem (notMem_empty j), card_empty] at h
      simp only [Fintype.card_fin, zero_add, pow_one, mul_one] at h
      have h' : (B.card : ℝ) * L ≤ (L : ℝ) ^ n := by exact_mod_cast h
      rw [mul_one_div, le_div_iff₀ hLpos]
      exact h'
    have hμ : (∑ nu ∈ B, (C nu : ℝ)) ≤ (M.card * (((L : ℝ) - (z : ℕ)) / L)) * B.card := by
      rw [hC]
      simp only
      rw [sum_card_filter_swap B M (fun nu a => vpos nu j < vpos nu a)]
      have hterm : ∀ a ∈ M, ((B.filter (fun nu => vpos nu j < vpos nu a)).card : ℝ) ≤
          (((L : ℝ) - (z : ℕ)) / L) * B.card := by
        intro a ha
        simp only [hM, Mset1, mem_filter, mem_univ, true_and] at ha
        obtain ⟨hai, haj, -, -⟩ := ha
        have hdisj : Disjoint (insert j (∅ : Finset (Fin n))) ({a} : Finset (Fin n)) := by
          simp [Ne.symm haj]
        have hfil : B.filter (fun nu => vpos nu j < vpos nu a) =
            boxF (insert j (∅ : Finset (Fin n)) ∪ ({a} : Finset (Fin n))) (Abox z j) := by
          ext nu
          rw [mem_filter, hBdef, insert_union,
            mem_boxF_Abox z j ((∅ : Finset (Fin n)) ∪ {a}) (by simp [Ne.symm haj]),
            mem_boxF_Abox z j ∅ (notMem_empty j)]
          simp
        have hr := boxF_ratio (insert j (∅ : Finset (Fin n))) ({a} : Finset (Fin n)) hdisj
          (Abox z j) (L - z) (fun v hv => card_Abox_le' z j v (by
            rw [mem_singleton] at hv; rw [hv]; exact haj))
        rw [← hfil, card_singleton] at hr
        simp only [Fintype.card_fin, pow_one] at hr
        have hr' : ((B.filter (fun nu => vpos nu j < vpos nu a)).card : ℝ) * L ≤
            B.card * ((L : ℝ) - (z : ℕ)) := by
          rw [← cast_sub_fin]; exact_mod_cast hr
        rw [mul_comm (((L : ℝ) - (z : ℕ)) / _), mul_div_assoc', le_div_iff₀ hLpos]
        linarith
      refine (sum_le_sum hterm).trans (le_of_eq ?_)
      rw [sum_const, nsmul_eq_mul]
      ring
    have hμ0 : 0 ≤ (M.card : ℝ) * (((L : ℝ) - (z : ℕ)) / L) := by
      have : (0 : ℝ) ≤ (L : ℝ) - (z : ℕ) := by rw [← cast_sub_fin]; positivity
      positivity
    refine (box_jensen B C 1 _ _ zero_le_one hμ0 hμ hqB).trans (le_of_eq ?_)
    rw [one_mul]
    ring
  refine (sum_le_sum (fun z _ => per_z z)).trans (le_of_eq ?_)
  rw [← mul_sum]
  congr 1
  rw [sum_fin_reflect L (fun w => 1 / (L : ℝ) * Real.log (1 + M.card * (w / L)))]
  unfold wsum
  apply sum_congr rfl
  intro r _
  norm_num

/-- **Step B**: the average over the vertex order. -/
theorem stepB_of {c : Fin n → Fin n → Fin (n - 1)} (hc : IsOF c) {i j : Fin n} (hij : i ≠ j)
    (hL : 1 ≤ L) (β : ℝ) (hβ : 0 ≤ β) :
    ∑ lam : Fin n → Fin L,
      (if vpos lam i < vpos lam j then Real.log (1 + β * (Mset1 lam c i j).card) else 0) ≤
      (L : ℝ) ^ n * ∑ r ∈ range L, ((r + 1 : ℝ) / (L : ℝ) ^ 2) *
        Real.log (1 + β * (((n : ℝ) - 2) * ((r + 1 : ℝ) / L) ^ 2)) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  -- the vertex `b a` with `X_{j, b a} = X_{i, a}`
  have hsurj : ∀ a, ∃ b, b ≠ j ∧ c j b = c i a := fun a => hc.surj j (c i a)
  choose bf hbf using hsurj
  set R : Finset (Fin n) := univ.filter (fun a => a ≠ i ∧ a ≠ j) with hR
  have hRcard : (R.card : ℝ) ≤ (n : ℝ) - 2 := by
    have hR' : R = univ \ insert i {j} := by
      ext t; simp [hR]
    have h2 : (insert i ({j} : Finset (Fin n))).card = 2 := by
      rw [card_insert_of_notMem (by simp [hij]), card_singleton]
    have hle : (insert i ({j} : Finset (Fin n))).card ≤ n := by
      simpa using card_le_univ (insert i ({j} : Finset (Fin n)))
    rw [hR', card_univ_diff, Fintype.card_fin, h2]
    rw [h2] at hle
    rw [Nat.cast_sub hle]; norm_num
  set P : (Fin n → Fin L) → Fin n → Prop := fun lam a => vpos lam i < vpos lam a ∧
    vpos lam i < vpos lam (bf a) with hP
  have hbfi : ∀ a, a ≠ i → a ≠ j → bf a ≠ i := by
    intro a hai haj h
    have e := (hbf a).2
    rw [h, hc.comm] at e
    exact haj (hc.inj hij (Ne.symm hai) e).symm
  have hsub : ∀ lam, Mset1 lam c i j ⊆ R.filter (P lam) := by
    intro lam a ha
    simp only [Mset1, mem_filter, mem_univ, true_and] at ha
    obtain ⟨hai, haj, hia, ht⟩ := ha
    simp only [hR, hP, mem_filter, mem_univ, true_and]
    refine ⟨⟨hai, haj⟩, hia, ?_⟩
    by_contra hcon
    have hlt : vpos lam (bf a) < vpos lam i := by
      have := vpos_ne lam (hbfi a hai haj); omega
    apply ht (bf a) hlt
    rw [hc.comm, (hbf a).2]
  rw [sum_split_value i]
  have per_x : ∀ x : Fin L, ∑ lam ∈ univ.filter (fun lam : Fin n → Fin L => lam i = x),
      (if vpos lam i < vpos lam j then Real.log (1 + β * (Mset1 lam c i j).card) else 0) ≤
      (L : ℝ) ^ n * (((L : ℝ) - (x : ℕ)) / (L : ℝ) ^ 2 *
        Real.log (1 + β * (((n : ℝ) - 2) * (((L : ℝ) - (x : ℕ)) / L) ^ 2))) := by
    intro x
    set B := boxF (insert i ({j} : Finset (Fin n))) (Abox x i) with hBdef
    have hiD : i ∉ ({j} : Finset (Fin n)) := by simp [hij]
    have hB : ∑ lam ∈ univ.filter (fun lam : Fin n → Fin L => lam i = x),
        (if vpos lam i < vpos lam j then Real.log (1 + β * (Mset1 lam c i j).card) else 0) =
        ∑ lam ∈ B, Real.log (1 + β * (Mset1 lam c i j).card) := by
      rw [← sum_filter, filter_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext lam
      rw [hBdef, mem_boxF_Abox x i _ hiD]
      simp
    rw [hB]
    have hmono : ∑ lam ∈ B, Real.log (1 + β * (Mset1 lam c i j).card) ≤
        ∑ lam ∈ B, Real.log (1 + β * ((R.filter (P lam)).card : ℕ)) := by
      apply sum_le_sum
      intro lam _
      apply Real.log_le_log (by positivity)
      have : ((Mset1 lam c i j).card : ℝ) ≤ ((R.filter (P lam)).card : ℕ) := by
        exact_mod_cast card_le_card (hsub lam)
      nlinarith
    refine hmono.trans ?_
    have hqB : (B.card : ℝ) ≤ (L : ℝ) ^ n * (((L : ℝ) - (x : ℕ)) / (L : ℝ) ^ 2) := by
      have h := boxF_card_le (insert i ({j} : Finset (Fin n))) (Abox x i)
        (fun v => if v = i then 1 else L - x) (fun v _ => card_Abox_le x i v)
      rw [prod_insert hiD, prod_singleton, if_pos rfl, if_neg (Ne.symm hij),
        card_insert_of_notMem hiD, card_singleton] at h
      simp only [Fintype.card_fin] at h
      have h' : (B.card : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ n * ((L : ℝ) - (x : ℕ)) := by
        rw [← cast_sub_fin]; exact_mod_cast (by simpa using h)
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      exact h'
    have hμ : (∑ lam ∈ B, ((R.filter (P lam)).card : ℝ)) ≤
        (((n : ℝ) - 2) * (((L : ℝ) - (x : ℕ)) / L) ^ 2) * B.card := by
      rw [sum_card_filter_swap B R (fun lam a => P lam a)]
      have hterm : ∀ a ∈ R, ((B.filter (fun lam => P lam a)).card : ℝ) ≤
          (((L : ℝ) - (x : ℕ)) / L) ^ 2 * B.card := by
        intro a ha
        simp only [hR, mem_filter, mem_univ, true_and] at ha
        obtain ⟨hai, haj⟩ := ha
        have hbj : bf a ≠ j := (hbf a).1
        have hbi : bf a ≠ i := hbfi a hai haj
        have hba : bf a ≠ a := by
          intro h
          have e := (hbf a).2
          rw [h, hc.comm a j, hc.comm a i] at e
          exact hij (hc.inj haj hai e).symm
        have hdisj : Disjoint (insert i ({j} : Finset (Fin n)))
            (insert a ({bf a} : Finset (Fin n))) := by
          rw [Finset.disjoint_left]
          intro u hu hv
          simp only [mem_insert, mem_singleton] at hu hv
          rcases hu with h0 | h0 <;> rcases hv with h | h <;> rw [h0] at h
          all_goals
            first
            | exact hai h.symm | exact hbi h.symm | exact haj h.symm | exact hbj h.symm
        have hfil : B.filter (fun lam => P lam a) =
            boxF (insert i ({j} : Finset (Fin n)) ∪ insert a ({bf a} : Finset (Fin n)))
              (Abox x i) := by
          ext lam
          rw [mem_filter, hBdef, insert_union,
            mem_boxF_Abox x i (({j} : Finset (Fin n)) ∪ insert a {bf a})
              (by simp [hij, hai.symm, hbi.symm]),
            mem_boxF_Abox x i ({j} : Finset (Fin n)) hiD]
          simp only [hP, mem_union, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
          tauto
        have hcardE : (insert a ({bf a} : Finset (Fin n))).card = 2 := by
          rw [card_insert_of_notMem (by simpa using hba.symm), card_singleton]
        have hr := boxF_ratio (insert i ({j} : Finset (Fin n)))
          (insert a ({bf a} : Finset (Fin n))) hdisj (Abox x i) (L - x)
          (fun v hv => card_Abox_le' x i v (by
            simp only [mem_insert, mem_singleton] at hv
            rcases hv with h | h <;> rw [h]
            · exact hai
            · exact hbi))
        rw [← hfil, hcardE] at hr
        simp only [Fintype.card_fin] at hr
        have hr' : ((B.filter (fun lam => P lam a)).card : ℝ) * (L : ℝ) ^ 2 ≤
            B.card * ((L : ℝ) - (x : ℕ)) ^ 2 := by
          rw [← cast_sub_fin]; exact_mod_cast hr
        rw [div_pow, mul_comm (((L : ℝ) - (x : ℕ)) ^ 2 / _), mul_div_assoc', le_div_iff₀
          (by positivity)]
        linarith
      refine (sum_le_sum hterm).trans ?_
      rw [sum_const, nsmul_eq_mul]
      have h0 : 0 ≤ (((L : ℝ) - (x : ℕ)) / L) ^ 2 * B.card := by positivity
      nlinarith
    have hμ0 : 0 ≤ ((n : ℝ) - 2) * (((L : ℝ) - (x : ℕ)) / L) ^ 2 := by
      have : (0 : ℝ) ≤ R.card := by positivity
      have : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
      positivity
    refine (box_jensen B (fun lam => (R.filter (P lam)).card) β _ _ hβ hμ0 hμ hqB).trans
      (le_of_eq ?_)
    ring
  refine (sum_le_sum (fun x _ => per_x x)).trans (le_of_eq ?_)
  rw [← mul_sum]
  congr 1
  exact sum_fin_reflect L (fun w => w / (L : ℝ) ^ 2 *
    Real.log (1 + β * (((n : ℝ) - 2) * (w / L) ^ 2)))

/-- **The expectation bound** (1-factorizations): `∑_{λ, ν} log N_{i,j} ≤ L^{2n} · PsiOF L n`. -/
theorem expect_of {c : Fin n → Fin n → Fin (n - 1)} (hc : IsOF c) {i j : Fin n} (hij : i ≠ j)
    (hL : 1 ≤ L) :
    ∑ lam : Fin n → Fin L, ∑ nu : Fin n → Fin L, Real.log (NvalOF lam nu c i j) ≤
      ((L : ℝ) ^ n) ^ 2 * PsiOF L n := by
  have h1 : ∀ lam : Fin n → Fin L, ∑ nu : Fin n → Fin L, Real.log (NvalOF lam nu c i j) ≤
      if vpos lam i < vpos lam j then (L : ℝ) ^ n * wsum 1 L (Mset1 lam c i j).card else 0 := by
    intro lam
    split_ifs with hcond
    · exact stepA_of c lam hL hcond
    · simp [NvalOF_of_not lam _ c i j hcond]
  refine (sum_le_sum (fun lam _ => h1 lam)).trans ?_
  have h2 : ∀ lam : Fin n → Fin L,
      (if vpos lam i < vpos lam j then (L : ℝ) ^ n * wsum 1 L (Mset1 lam c i j).card else 0) =
      (L : ℝ) ^ n * ∑ r ∈ range L, (1 / (L : ℝ)) *
        (if vpos lam i < vpos lam j then
          Real.log (1 + ((r + 1 : ℝ) / L) * (Mset1 lam c i j).card) else 0) := by
    intro lam
    split_ifs
    · unfold wsum
      congr 1
      apply sum_congr rfl
      intro r _
      norm_num
      left
      ring_nf
    · simp
  rw [sum_congr rfl (fun lam _ => h2 lam), ← mul_sum, sum_comm]
  have h3 : ∀ r ∈ range L, ∑ lam : Fin n → Fin L, (1 / (L : ℝ)) *
      (if vpos lam i < vpos lam j then
        Real.log (1 + ((r + 1 : ℝ) / L) * (Mset1 lam c i j).card) else 0) ≤
      (1 / (L : ℝ)) * ((L : ℝ) ^ n * ∑ r' ∈ range L,
        ((r' + 1 : ℝ) / (L : ℝ) ^ 2) *
        Real.log (1 + ((r + 1 : ℝ) / L) * (((n : ℝ) - 2) * ((r' + 1 : ℝ) / L) ^ 2))) := by
    intro r _
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (stepB_of hc hij hL _ (by positivity)) (by positivity)
  have hLn : (0 : ℝ) ≤ (L : ℝ) ^ n := by positivity
  refine (mul_le_mul_of_nonneg_left (sum_le_sum h3) hLn).trans (le_of_eq ?_)
  unfold PsiOF wsum
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r' _
  apply sum_congr rfl
  intro r _
  norm_num
  ring_nf

end LinialLuria
