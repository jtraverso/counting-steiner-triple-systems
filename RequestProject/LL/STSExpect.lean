/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LL.STSReveal
public import RequestProject.LL.Expect
public import RequestProject.LL.Estimates

/-!
# The expectation of `log N_{i,j}` (Steiner triple systems)

For a fixed Steiner quasigroup `T` and a fixed pair `i ≠ j` we bound the sum of
`log (NvalSTS lam nu T i j)` over all label maps `lam, nu : Fin n → Fin L`, i.e. `L^{2n}`
times the expectation `E[log N_{i,j}]` of the paper:

* `stepA_sts` : the average over the edge order (`nu`), for a fixed vertex order; this is
  Jensen's inequality conditioned on the position of `j` in the star of `i`
  (Lemmas 3.3 and 3.4 of the paper);
* `stepB_sts` : the average over the vertex order (`lam`); this is Jensen's inequality
  conditioned on the position of `i` (Lemmas 3.1 and 3.2 of the paper);
* `expect_sts` : the combination, `∑ log N_{i,j} ≤ L^{2n} · PsiSTS L n`.
-/

@[expose] public section

open Finset

namespace LinialLuria

variable {n L : ℕ}

/-- The vertices `t ∉ {i, j, k}` (`k = X_{i,j}`) such that `t`, `X_{i,t}` and `X_{j,t}` all
come after `i`: these are the vertices that are not ruled out for `X_{i,j}` by the entries
involving the vertices preceding `i` (the set `M_{i,j} ∖ {k}` of the paper). -/
def Mset (lam : Fin n → Fin L) (T : Fin n → Fin n → Fin n) (i j : Fin n) : Finset (Fin n) :=
  univ.filter (fun t => t ≠ i ∧ t ≠ j ∧ t ≠ T i j ∧ vpos lam i < vpos lam t ∧
    vpos lam i < vpos lam (T i t) ∧ vpos lam i < vpos lam (T j t))

lemma NvalSTS_eq (lam nu : Fin n → Fin L) (T : Fin n → Fin n → Fin n) (i j : Fin n)
    (h : vpos lam i < vpos lam j ∧ vpos lam i < vpos lam (T i j)) :
    NvalSTS lam nu T i j = if vpos nu j < vpos nu (T i j) then
      1 + ((Mset lam T i j).filter
        (fun t => vpos nu j < vpos nu t ∧ vpos nu j < vpos nu (T i t))).card else 1 := by
  unfold NvalSTS Mset
  simp only [h, true_and]
  split_ifs
  · rw [filter_filter]
    congr 2
    ext t
    simp only [mem_filter, mem_univ, true_and]
    tauto
  · rfl

lemma NvalSTS_of_not (lam nu : Fin n → Fin L) (T : Fin n → Fin n → Fin n) (i j : Fin n)
    (h : ¬ (vpos lam i < vpos lam j ∧ vpos lam i < vpos lam (T i j))) :
    NvalSTS lam nu T i j = 1 := by
  unfold NvalSTS
  rw [if_neg]
  tauto

/-- **Step A**: the average over the edge order. -/
theorem stepA_sts {T : Fin n → Fin n → Fin n} (hT : IsSQ T) {i j : Fin n} (hij : i ≠ j)
    (lam : Fin n → Fin L) (hL : 1 ≤ L)
    (hc : vpos lam i < vpos lam j ∧ vpos lam i < vpos lam (T i j)) :
    ∑ nu : Fin n → Fin L, Real.log (NvalSTS lam nu T i j) ≤
      (L : ℝ) ^ n * wsum 2 L (Mset lam T i j).card := by
  set k := T i j with hk
  have hkj : k ≠ j := hT.ne_right hij
  have hki : k ≠ i := hT.ne_left hij
  set M := Mset lam T i j with hM
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set C : (Fin n → Fin L) → ℕ := fun nu =>
    (M.filter (fun t => vpos nu j < vpos nu t ∧ vpos nu j < vpos nu (T i t))).card with hC
  rw [sum_split_value j]
  have per_z : ∀ z : Fin L, ∑ nu ∈ univ.filter (fun nu : Fin n → Fin L => nu j = z),
      Real.log (NvalSTS lam nu T i j) ≤
      (L : ℝ) ^ n * (((L : ℝ) - (z : ℕ)) / (L : ℝ) ^ 2 *
        Real.log (1 + M.card * (((L : ℝ) - (z : ℕ)) / L) ^ 2)) := by
    intro z
    set B := boxF (insert j {k}) (Abox z j) with hBdef
    have hB : ∑ nu ∈ univ.filter (fun nu : Fin n → Fin L => nu j = z),
        Real.log (NvalSTS lam nu T i j) = ∑ nu ∈ B, Real.log (1 + 1 * (C nu : ℝ)) := by
      have e1 : ∀ nu ∈ univ.filter (fun nu : Fin n → Fin L => nu j = z),
          Real.log (NvalSTS lam nu T i j) =
          if vpos nu j < vpos nu k then Real.log (1 + 1 * (C nu : ℝ)) else 0 := by
        intro nu _
        rw [NvalSTS_eq lam nu T i j hc, ← hk]
        split_ifs
        · simp only [hC, hM]; push_cast; ring_nf
        · simp
      rw [sum_congr rfl e1, ← sum_filter, filter_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext nu
      rw [hBdef, mem_boxF_Abox z j {k} (by simpa using hkj.symm)]
      simp
    rw [hB]
    have hqB : (B.card : ℝ) ≤ (L : ℝ) ^ n * (((L : ℝ) - (z : ℕ)) / (L : ℝ) ^ 2) := by
      have h := boxF_card_le (insert j {k}) (Abox z j) (fun v => if v = j then 1 else L - z)
        (fun v _ => card_Abox_le z j v)
      rw [prod_insert (by simpa using hkj.symm), prod_singleton, if_pos rfl, if_neg hkj,
        card_insert_of_notMem (by simpa using hkj.symm), card_singleton] at h
      simp only [Fintype.card_fin] at h
      have h' : (B.card : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ n * ((L : ℝ) - (z : ℕ)) := by
        rw [← cast_sub_fin]; exact_mod_cast (by simpa using h)
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      exact h'
    have hμ : (∑ nu ∈ B, (C nu : ℝ)) ≤ (M.card * (((L : ℝ) - (z : ℕ)) / L) ^ 2) * B.card := by
      rw [hC]
      simp only
      rw [sum_card_filter_swap B M
        (fun nu t => vpos nu j < vpos nu t ∧ vpos nu j < vpos nu (T i t))]
      have hterm : ∀ t ∈ M, ((B.filter (fun nu =>
          vpos nu j < vpos nu t ∧ vpos nu j < vpos nu (T i t))).card : ℝ) ≤
          (((L : ℝ) - (z : ℕ)) / L) ^ 2 * B.card := by
        intro t ht
        simp only [hM, Mset, mem_filter, mem_univ, true_and] at ht
        obtain ⟨hti, htj, htk, -, -, -⟩ := ht
        have hat : T i t ≠ t := hT.ne_right (Ne.symm hti)
        have haj : T i t ≠ j := by
          intro h; apply htk; rw [← h, hT.invol]
        have hak : T i t ≠ k := by
          intro h; apply htj; rw [← hT.invol i t, h, hk, hT.invol]
        have hdisj : Disjoint (insert j ({k} : Finset (Fin n))) (insert t ({T i t} : Finset (Fin n))) := by
          simp only [disjoint_insert_left, disjoint_singleton_left, mem_insert, mem_singleton]
          refine ⟨?_, ?_⟩ <;> push_neg
          · exact ⟨Ne.symm htj, Ne.symm haj⟩
          · exact ⟨Ne.symm htk, Ne.symm hak⟩
        have hfil : B.filter (fun nu => vpos nu j < vpos nu t ∧ vpos nu j < vpos nu (T i t)) =
            boxF (insert j ({k} : Finset (Fin n)) ∪ insert t ({T i t} : Finset (Fin n))) (Abox z j) := by
          ext nu
          rw [mem_filter, hBdef, insert_union,
            mem_boxF_Abox z j ({k} ∪ insert t {T i t}) (by simp [hkj.symm, htj.symm, haj.symm]),
            mem_boxF_Abox z j {k} (by simpa using hkj.symm)]
          simp only [mem_union, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
          tauto
        have hr := boxF_ratio (insert j ({k} : Finset (Fin n))) (insert t ({T i t} : Finset (Fin n))) hdisj (Abox z j) (L - z)
          (fun v hv => card_Abox_le' z j v (by
            simp only [mem_insert, mem_singleton] at hv
            rcases hv with rfl | rfl
            · exact htj
            · exact haj))
        rw [← hfil, card_insert_of_notMem (by simpa using hat.symm), card_singleton] at hr
        simp only [Fintype.card_fin] at hr
        have hr' : ((B.filter (fun nu =>
            vpos nu j < vpos nu t ∧ vpos nu j < vpos nu (T i t))).card : ℝ) * (L : ℝ) ^ 2 ≤
            B.card * ((L : ℝ) - (z : ℕ)) ^ 2 := by
          rw [← cast_sub_fin]; exact_mod_cast hr
        rw [div_pow, mul_comm (((L : ℝ) - (z : ℕ)) ^ 2 / _), mul_div_assoc', le_div_iff₀
          (by positivity)]
        linarith
      refine (sum_le_sum hterm).trans (le_of_eq ?_)
      rw [sum_const, nsmul_eq_mul]
      ring
    refine (box_jensen B C 1 _ _ zero_le_one (by positivity) hμ hqB).trans (le_of_eq ?_)
    rw [one_mul]
    ring
  refine (sum_le_sum (fun z _ => per_z z)).trans (le_of_eq ?_)
  rw [← mul_sum]
  congr 1
  rw [sum_fin_reflect L (fun w => w / (L : ℝ) ^ 2 * Real.log (1 + M.card * (w / L) ^ 2))]
  unfold wsum
  apply sum_congr rfl
  intro r _
  norm_num

/-- **Step B**: the average over the vertex order. -/
theorem stepB_sts {T : Fin n → Fin n → Fin n} (hT : IsSQ T) {i j : Fin n} (hij : i ≠ j)
    (hL : 1 ≤ L) (β : ℝ) (hβ : 0 ≤ β) :
    ∑ lam : Fin n → Fin L,
      (if vpos lam i < vpos lam j ∧ vpos lam i < vpos lam (T i j) then
        Real.log (1 + β * (Mset lam T i j).card) else 0) ≤
      (L : ℝ) ^ n * ∑ r ∈ range L, ((r + 1 : ℝ) ^ 2 / (L : ℝ) ^ 3) *
        Real.log (1 + β * (((n : ℝ) - 3) * ((r + 1 : ℝ) / L) ^ 3)) := by
  set k := T i j with hk
  have hkj : k ≠ j := hT.ne_right hij
  have hki : k ≠ i := hT.ne_left hij
  have hTjk : T j k = i := by rw [hk, ← hT.comm i j, hT.invol]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set R : Finset (Fin n) := univ.filter (fun t => t ≠ i ∧ t ≠ j ∧ t ≠ k) with hR
  have hRcard : (R.card : ℝ) ≤ (n : ℝ) - 3 := by
    have hR' : R = univ \ insert i (insert j {k}) := by
      ext t; simp [hR]
    have h3 : (insert i (insert j ({k} : Finset (Fin n)))).card = 3 := by
      rw [card_insert_of_notMem (by simp [hij, hki.symm]),
        card_insert_of_notMem (by simp [hkj.symm]), card_singleton]
    have hle : (insert i (insert j ({k} : Finset (Fin n)))).card ≤ n := by
      simpa using card_le_univ (insert i (insert j ({k} : Finset (Fin n))))
    rw [hR', card_univ_diff, Fintype.card_fin, h3]
    rw [h3] at hle
    rw [Nat.cast_sub hle]; norm_num
  set P : (Fin n → Fin L) → Fin n → Prop := fun lam t => vpos lam i < vpos lam t ∧
    vpos lam i < vpos lam (T i t) ∧ vpos lam i < vpos lam (T j t) with hP
  have hMset : ∀ lam, Mset lam T i j = R.filter (P lam) := by
    intro lam
    ext t
    simp only [Mset, hR, hP, mem_filter, mem_univ, true_and]
    tauto
  rw [sum_split_value i]
  have per_x : ∀ x : Fin L, ∑ lam ∈ univ.filter (fun lam : Fin n → Fin L => lam i = x),
      (if vpos lam i < vpos lam j ∧ vpos lam i < vpos lam k then
        Real.log (1 + β * (Mset lam T i j).card) else 0) ≤
      (L : ℝ) ^ n * (((L : ℝ) - (x : ℕ)) ^ 2 / (L : ℝ) ^ 3 *
        Real.log (1 + β * (((n : ℝ) - 3) * (((L : ℝ) - (x : ℕ)) / L) ^ 3))) := by
    intro x
    set B := boxF (insert i ({j, k} : Finset (Fin n))) (Abox x i) with hBdef
    have hiD : i ∉ ({j, k} : Finset (Fin n)) := by simp [hij, hki.symm]
    have hB : ∑ lam ∈ univ.filter (fun lam : Fin n → Fin L => lam i = x),
        (if vpos lam i < vpos lam j ∧ vpos lam i < vpos lam k then
          Real.log (1 + β * (Mset lam T i j).card) else 0) =
        ∑ lam ∈ B, Real.log (1 + β * ((R.filter (P lam)).card : ℕ)) := by
      rw [← sum_filter, filter_filter]
      apply sum_congr
      · ext lam
        rw [hBdef, mem_boxF_Abox x i _ hiD]
        simp
      · intro lam _
        rw [hMset lam]
    rw [hB]
    have hqB : (B.card : ℝ) ≤ (L : ℝ) ^ n * (((L : ℝ) - (x : ℕ)) ^ 2 / (L : ℝ) ^ 3) := by
      have h := boxF_card_le (insert i ({j, k} : Finset (Fin n))) (Abox x i)
        (fun v => if v = i then 1 else L - x) (fun v _ => card_Abox_le x i v)
      rw [prod_insert hiD, prod_insert (by simpa using hkj.symm), prod_singleton, if_pos rfl,
        if_neg (Ne.symm hij), if_neg hki, card_insert_of_notMem hiD,
        card_insert_of_notMem (by simpa using hkj.symm), card_singleton] at h
      simp only [Fintype.card_fin] at h
      have h' : (B.card : ℝ) * (L : ℝ) ^ 3 ≤ (L : ℝ) ^ n * ((L : ℝ) - (x : ℕ)) ^ 2 := by
        rw [← cast_sub_fin]; exact_mod_cast (by simpa [sq] using h)
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      exact h'
    have hμ : (∑ lam ∈ B, ((R.filter (P lam)).card : ℝ)) ≤
        (((n : ℝ) - 3) * (((L : ℝ) - (x : ℕ)) / L) ^ 3) * B.card := by
      rw [sum_card_filter_swap B R (fun lam t => P lam t)]
      have hterm : ∀ t ∈ R, ((B.filter (fun lam => P lam t)).card : ℝ) ≤
          (((L : ℝ) - (x : ℕ)) / L) ^ 3 * B.card := by
        intro t ht
        simp only [hR, mem_filter, mem_univ, true_and] at ht
        obtain ⟨hti, htj, htk⟩ := ht
        set a := T i t with ha
        set b := T j t with hb
        have hat : a ≠ t := hT.ne_right (Ne.symm hti)
        have hai : a ≠ i := hT.ne_left (Ne.symm hti)
        have haj : a ≠ j := by intro h; apply htk; rw [hk, ← h, ha, hT.invol]
        have hak : a ≠ k := by
          intro h; apply htj; rw [← hT.invol i t, ← ha, h, hk, hT.invol]
        have hbt : b ≠ t := hT.ne_right (Ne.symm htj)
        have hbj : b ≠ j := hT.ne_left (Ne.symm htj)
        have hbi : b ≠ i := by
          intro h; apply htk; rw [hk, ← hT.comm i j, ← h, hb, hT.invol]
        have hbk : b ≠ k := by
          intro h; apply hti; rw [← hT.invol j t, ← hb, h, hTjk]
        have hba : b ≠ a := by
          intro h
          have e : T t j = T t i := by rw [hT.comm, hT.comm i t]; exact h
          exact hij (hT.inj e).symm
        have hdisj : Disjoint (insert i ({j, k} : Finset (Fin n)))
            (insert t ({a, b} : Finset (Fin n))) := by
          rw [Finset.disjoint_left]
          intro u hu hv
          simp only [mem_insert, mem_singleton] at hu hv
          rcases hu with h0 | h0 | h0 <;> rcases hv with h | h | h <;> rw [h0] at h
          all_goals
            first
            | exact hti h.symm | exact hai h.symm | exact hbi h.symm
            | exact htj h.symm | exact haj h.symm | exact hbj h.symm
            | exact htk h.symm | exact hak h.symm | exact hbk h.symm
        have hfil : B.filter (fun lam => P lam t) =
            boxF (insert i ({j, k} : Finset (Fin n)) ∪ insert t ({a, b} : Finset (Fin n)))
              (Abox x i) := by
          ext lam
          rw [mem_filter, hBdef, insert_union,
            mem_boxF_Abox x i (({j, k} : Finset (Fin n)) ∪ insert t {a, b})
              (by simp [hij, hki.symm, hti.symm, hai.symm, hbi.symm]),
            mem_boxF_Abox x i ({j, k} : Finset (Fin n)) hiD]
          simp only [hP, mem_union, mem_insert, mem_singleton, or_assoc, forall_eq_or_imp,
            forall_eq, ha, hb]
          tauto
        have hcardE : (insert t ({a, b} : Finset (Fin n))).card = 3 := by
          rw [card_insert_of_notMem (by simp [hat.symm, hbt.symm]),
            card_insert_of_notMem (by simpa using hba.symm), card_singleton]
        have hr := boxF_ratio (insert i ({j, k} : Finset (Fin n)))
          (insert t ({a, b} : Finset (Fin n))) hdisj (Abox x i) (L - x)
          (fun v hv => card_Abox_le' x i v (by
            simp only [mem_insert, mem_singleton] at hv
            rcases hv with rfl | rfl | rfl
            · exact hti
            · exact hai
            · exact hbi))
        rw [← hfil, hcardE] at hr
        simp only [Fintype.card_fin] at hr
        have hr' : ((B.filter (fun lam => P lam t)).card : ℝ) * (L : ℝ) ^ 3 ≤
            B.card * ((L : ℝ) - (x : ℕ)) ^ 3 := by
          rw [← cast_sub_fin]; exact_mod_cast hr
        rw [div_pow, mul_comm (((L : ℝ) - (x : ℕ)) ^ 3 / _), mul_div_assoc', le_div_iff₀
          (by positivity)]
        linarith
      refine (sum_le_sum hterm).trans ?_
      rw [sum_const, nsmul_eq_mul]
      have h0 : 0 ≤ (((L : ℝ) - (x : ℕ)) / L) ^ 3 * B.card := by
        have : (0 : ℝ) ≤ (L : ℝ) - (x : ℕ) := by rw [← cast_sub_fin]; positivity
        positivity
      nlinarith
    have hμ0 : 0 ≤ ((n : ℝ) - 3) * (((L : ℝ) - (x : ℕ)) / L) ^ 3 := by
      have : (0 : ℝ) ≤ (L : ℝ) - (x : ℕ) := by rw [← cast_sub_fin]; positivity
      have : (0 : ℝ) ≤ R.card := by positivity
      have : (0 : ℝ) ≤ (n : ℝ) - 3 := by linarith
      positivity
    refine (box_jensen B (fun lam => (R.filter (P lam)).card) β _ _ hβ hμ0 hμ hqB).trans
      (le_of_eq ?_)
    ring
  refine (sum_le_sum (fun x _ => per_x x)).trans (le_of_eq ?_)
  rw [← mul_sum]
  congr 1
  exact sum_fin_reflect L (fun w => w ^ 2 / (L : ℝ) ^ 3 *
    Real.log (1 + β * (((n : ℝ) - 3) * (w / L) ^ 3)))

/-- **The expectation bound**: `∑_{λ, ν} log N_{i,j} ≤ L^{2n} · PsiSTS L n`, i.e.
`E[log N_{i,j}] ≤ PsiSTS L n`. -/
theorem expect_sts {T : Fin n → Fin n → Fin n} (hT : IsSQ T) {i j : Fin n} (hij : i ≠ j)
    (hL : 1 ≤ L) :
    ∑ lam : Fin n → Fin L, ∑ nu : Fin n → Fin L, Real.log (NvalSTS lam nu T i j) ≤
      ((L : ℝ) ^ n) ^ 2 * PsiSTS L n := by
  have h1 : ∀ lam : Fin n → Fin L, ∑ nu : Fin n → Fin L, Real.log (NvalSTS lam nu T i j) ≤
      if vpos lam i < vpos lam j ∧ vpos lam i < vpos lam (T i j) then
        (L : ℝ) ^ n * wsum 2 L (Mset lam T i j).card else 0 := by
    intro lam
    split_ifs with hc
    · exact stepA_sts hT hij lam hL hc
    · simp [NvalSTS_of_not lam _ T i j hc]
  refine (sum_le_sum (fun lam _ => h1 lam)).trans ?_
  have h2 : ∀ lam : Fin n → Fin L,
      (if vpos lam i < vpos lam j ∧ vpos lam i < vpos lam (T i j) then
        (L : ℝ) ^ n * wsum 2 L (Mset lam T i j).card else 0) =
      (L : ℝ) ^ n * ∑ r ∈ range L, ((r + 1 : ℝ) / (L : ℝ) ^ 2) *
        (if vpos lam i < vpos lam j ∧ vpos lam i < vpos lam (T i j) then
          Real.log (1 + ((r + 1 : ℝ) / L) ^ 2 * (Mset lam T i j).card) else 0) := by
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
  have h3 : ∀ r ∈ range L, ∑ lam : Fin n → Fin L, ((r + 1 : ℝ) / (L : ℝ) ^ 2) *
      (if vpos lam i < vpos lam j ∧ vpos lam i < vpos lam (T i j) then
        Real.log (1 + ((r + 1 : ℝ) / L) ^ 2 * (Mset lam T i j).card) else 0) ≤
      ((r + 1 : ℝ) / (L : ℝ) ^ 2) * ((L : ℝ) ^ n * ∑ r' ∈ range L,
        ((r' + 1 : ℝ) ^ 2 / (L : ℝ) ^ 3) *
        Real.log (1 + ((r + 1 : ℝ) / L) ^ 2 * (((n : ℝ) - 3) * ((r' + 1 : ℝ) / L) ^ 3))) := by
    intro r _
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (stepB_sts hT hij hL _ (by positivity)) (by positivity)
  have hLn : (0 : ℝ) ≤ (L : ℝ) ^ n := by positivity
  refine (mul_le_mul_of_nonneg_left (sum_le_sum h3) hLn).trans (le_of_eq ?_)
  unfold PsiSTS wsum
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r' _
  apply sum_congr rfl
  intro r _
  norm_num
  ring_nf

end LinialLuria
