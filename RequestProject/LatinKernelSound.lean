/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LatinKernel
public import RequestProject.LatinCompute
public import RequestProject.LatinRowSym

/-!
# Soundness of the kernel-checkable certificate checker for `L(n)`
-/

@[expose] public section

open Finset

namespace STS.LatinKernel

open LatinCompute

/-! ### Bits -/

lemma bit_eq (m i : ℕ) : bit m i = m.testBit i := by
  unfold bit
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff, Nat.beq_eq,
    decide_eq_true_eq]

lemma testBit_lowBits {q : ℕ} (hq : q < 64) : lowBits.testBit q = decide (q % 8 = 0) := by
  have : ∀ q < 64, lowBits.testBit q = decide (q % 8 = 0) := by decide
  exact this q hq

lemma tauOf_lt (c s : ℕ) : tauOf c s < 8 := Nat.mod_lt _ (by norm_num)

lemma testBit_relab_term (y s τ j t : ℕ) (hτ : τ < 8) (hj : j < 8) (ht : t < 8) :
    (((y >>> s) &&& lowBits) <<< τ).testBit (8 * j + t) = (decide (τ = t) && y.testBit (8 * j + s)) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight]
  by_cases h : τ = t
  · subst h
    have h1 : 8 * j + τ - τ = 8 * j := by omega
    rw [h1, testBit_lowBits (by omega), Nat.add_comm s]
    simp
  · simp only [h, decide_false, Bool.false_and]
    by_cases h2 : 8 * j + t ≥ τ
    · rw [testBit_lowBits (by omega)]
      have : ¬ (8 * j + t - τ) % 8 = 0 := by omega
      simp [this]
    · simp [h2]

lemma testBit_relab (n y c j t : ℕ) (hj : j < 8) (ht : t < 8) :
    (relab n y c).testBit (8 * j + t) =
      (List.range n).any (fun s => decide (tauOf c s = t) && y.testBit (8 * j + s)) := by
  unfold relab
  rw [testBit_foldl _ (fun s i => (((y >>> s) &&& lowBits) <<< tauOf c s).testBit i)]
  · simp only [Nat.zero_testBit, Bool.false_or]
    congr 1
    funext s
    exact testBit_relab_term y s _ j t (tauOf_lt c s) hj ht
  · intro acc a i
    rw [Nat.testBit_or]

lemma permOk_spec {n c : ℕ} (h : permOk n c = true) :
    (∀ s < n, tauOf c s < n) ∧ (∀ t < n, ∃ s < n, tauOf c s = t) := by
  unfold permOk at h
  rw [Nat.beq_eq] at h
  have key : ∀ i, ((List.range n).foldl (fun acc s => acc ||| 2 ^ tauOf c s) 0).testBit i =
      (List.range n).any (fun s => decide (tauOf c s = i)) := by
    intro i
    rw [testBit_foldl _ (fun s i => decide (tauOf c s = i))]
    · simp
    · intro acc a i
      rw [Nat.testBit_or, Nat.testBit_two_pow]
  rw [h] at key
  constructor
  · intro s hs
    have := key (tauOf c s)
    rw [Nat.testBit_two_pow_sub_one] at this
    have h2 : (List.range n).any (fun s' => decide (tauOf c s' = tauOf c s)) = true :=
      List.any_eq_true.2 ⟨s, List.mem_range.2 hs, by simp⟩
    rw [h2] at this
    simpa using this
  · intro t ht
    have := key t
    rw [Nat.testBit_two_pow_sub_one] at this
    simp only [ht, decide_true] at this
    obtain ⟨s, hs, hst⟩ := List.any_eq_true.1 this.symm
    exact ⟨s, List.mem_range.1 hs, by simpa using hst⟩

lemma exists_perm_of_permOk {n c : ℕ} (h : permOk n c = true) :
    ∃ τ : Equiv.Perm (Fin n), ∀ s : Fin n, (τ s : ℕ) = tauOf c s := by
  obtain ⟨h1, h2⟩ := permOk_spec h
  let f : Fin n → Fin n := fun s => ⟨tauOf c s, h1 s s.2⟩
  have hs : Function.Surjective f := by
    intro t
    obtain ⟨s, hs, hst⟩ := h2 t t.2
    exact ⟨⟨s, hs⟩, Fin.ext hst⟩
  have hb : Function.Bijective f := (Fintype.bijective_iff_surjective_and_card f).2 ⟨hs, rfl⟩
  exact ⟨Equiv.ofBijective f hb, fun s => rfl⟩

lemma dec_relab {n : ℕ} (hn : n ≤ 8) {c : ℕ} {τ : Equiv.Perm (Fin n)}
    (hτ : ∀ s : Fin n, (τ s : ℕ) = tauOf c s) (y : ℕ) :
    dec n (relab n y c) = transform (dec n y) 1 τ := by
  funext j
  ext t
  simp only [dec, transform, mem_filter, mem_univ, true_and, mem_map_equiv, Equiv.Perm.coe_one,
    id]
  rw [testBit_relab n y c j t (by omega) (by omega)]
  rw [List.any_eq_true]
  constructor
  · rintro ⟨s, hs, hst⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hst
    have hs' : s < n := List.mem_range.1 hs
    have : τ.symm t = ⟨s, hs'⟩ := by
      rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [hτ]; exact hst.1.symm
    rw [this]; exact Finset.mem_filter.2 ⟨mem_univ _, hst.2⟩
  · intro h
    refine ⟨τ.symm t, List.mem_range.2 (τ.symm t).2, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, (Finset.mem_filter.1 h).2⟩
    rw [← hτ]; simp

/-! ### Sorting the columns -/

lemma ins_eq (a : ℕ) (l : List ℕ) : ins a l = l.orderedInsert (· ≤ ·) a := by
  induction l with
  | nil => simp [ins]
  | cons b l ih =>
    simp only [ins, List.orderedInsert_cons, ih]
    by_cases h : a ≤ b
    · have : Nat.ble a b = true := by rw [Nat.ble_eq]; exact h
      simp [this, h]
    · have : Nat.ble a b = false := by
        rw [← Bool.not_eq_true, Nat.ble_eq]; exact h
      simp [this, h]

lemma isort_eq (l : List ℕ) : isort l = l.insertionSort (· ≤ ·) := by
  induction l with
  | nil => simp [isort]
  | cons a l ih => simp [isort, List.insertionSort_cons, ih, ins_eq]

lemma testBit_ofCols (l : List ℕ) (hl : ∀ c ∈ l, c < 256) (j t : ℕ) (hj : j < l.length)
    (ht : t < 8) : (ofCols l).testBit (8 * j + t) = l[j].testBit t := by
  induction l generalizing j with
  | nil => simp at hj
  | cons c l ih =>
    have hc : c < 2 ^ 8 := by have := hl c (by simp); norm_num; omega
    have h1 : ofCols (c :: l) = 2 ^ 8 * ofCols l + c := by simp only [ofCols]; ring
    rw [h1, Nat.testBit_two_pow_mul_add _ hc]
    cases j with
    | zero => simp [ht]
    | succ j =>
      have h2 : ¬ 8 * (j + 1) + t < 8 := by omega
      have h3 : 8 * (j + 1) + t - 8 = 8 * j + t := by omega
      rw [if_neg h2, h3, ih (fun c hc => hl c (by simp [hc])) j (by simpa using hj)]
      simp

lemma testBit_col (z k t : ℕ) (ht : t < 8) : ((z >>> (8 * k)) % 256).testBit t =
    z.testBit (8 * k + t) := by
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [ht]

lemma cols_eq (n z : ℕ) : cols n z = List.ofFn (fun j : Fin n => (z >>> (8 * (j : ℕ))) % 256) := by
  apply List.ext_getElem (by simp [cols])
  intro i h1 h2
  simp [cols]

lemma dec_sort {n : ℕ} (hn : n ≤ 8) (z : ℕ) :
    ∃ π : Equiv.Perm (Fin n), dec n (ofCols (isort (cols n z))) = transform (dec n z) π 1 := by
  set f : Fin n → ℕ := fun j => (z >>> (8 * (j : ℕ))) % 256 with hf
  refine ⟨Tuple.sort f, ?_⟩
  have hs : isort (cols n z) = List.ofFn (f ∘ Tuple.sort f) := by
    rw [isort_eq, cols_eq]
    apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    · exact List.pairwise_insertionSort _ _
    · rw [List.pairwise_ofFn]
      intro i j hij
      exact Tuple.monotone_sort f hij.le
    · exact (List.perm_insertionSort _ _).trans (Equiv.Perm.ofFn_comp_perm _ f).symm
  funext j
  ext t
  simp only [dec, transform, mem_filter, mem_univ, true_and, Equiv.Perm.coe_one,
    mem_map_equiv, Equiv.Perm.one_symm, id]
  rw [hs, testBit_ofCols _ _ j t (by simp) (by omega)]
  · simp only [List.getElem_ofFn, Function.comp_apply, hf]
    rw [testBit_col _ _ _ (by omega)]
  · intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc
    exact Nat.mod_lt _ (by norm_num)

lemma E_canon {n : ℕ} (hn : n ≤ 8) {c : ℕ} (hc : permOk n c = true) (y r : ℕ) :
    E n (dec n (canon n y c)) r = E n (dec n y) r := by
  obtain ⟨τ, hτ⟩ := exists_perm_of_permOk hc
  obtain ⟨π, hπ⟩ := dec_sort hn (relab n y c)
  unfold canon
  rw [hπ, E_transform, dec_relab hn hτ, E_transform]

/-! ### Lookup trees -/

lemma KT.find_mem {T : KT} {z r v : ℕ} (h : T.find z = some (r, v)) : (z, r, v) ∈ T.toList := by
  induction T with
  | leaf => simp [KT.find] at h
  | node l k r' v' t ihl iht =>
    simp only [KT.find] at h
    simp only [KT.toList, List.mem_append, List.mem_cons]
    by_cases h1 : Nat.beq z k = true
    · rw [h1] at h
      simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
      rw [Nat.beq_eq] at h1
      subst h1
      right; left; rw [h.1, h.2]
    · rw [Bool.not_eq_true] at h1
      rw [h1] at h
      simp only [Bool.cond_false] at h
      by_cases h2 : Nat.blt z k = true
      · rw [h2] at h; exact Or.inl (ihl h)
      · rw [Bool.not_eq_true] at h2; rw [h2] at h; exact Or.inr (Or.inr (iht h))

/-! ### Rows -/

lemma testBit_maskL (l : List ℕ) (hl : ∀ s ∈ l, s < 8) (j j' t : ℕ) (ht : t < 8) :
    (maskL j l).testBit (8 * j' + t) = true ↔ ∃ i, ∃ h : i < l.length, j + i = j' ∧ l[i] = t := by
  induction l generalizing j with
  | nil => simp [maskL]
  | cons s l ih =>
    have hs : s < 8 := hl s (by simp)
    simp only [maskL, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
    rw [ih (fun s hs => hl s (by simp [hs])) (j + 1)]
    constructor
    · rintro (h | ⟨i, hi, h1, h2⟩)
      · exact ⟨0, by simp, by omega, by simp; omega⟩
      · exact ⟨i + 1, by simpa using hi, by omega, by simpa using h2⟩
    · rintro ⟨i, hi, h1, h2⟩
      cases i with
      | zero => left; simp at h2; omega
      | succ i => right; exact ⟨i, by simpa using hi, by omega, by simpa using h2⟩

lemma dec_or_maskL_ofFn {n : ℕ} (hn : n ≤ 8) (x : ℕ) (σ : Equiv.Perm (Fin n)) :
    dec n (x ||| maskL 0 (List.ofFn (fun j => (σ j : ℕ)))) = addRow (dec n x) σ := by
  funext j
  ext t
  simp only [dec, addRow, mem_filter, mem_univ, true_and, mem_insert, Nat.testBit_or,
    Bool.or_eq_true]
  rw [testBit_maskL _ (by intro s hs; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hs; omega) 0 j t
    (by omega)]
  constructor
  · rintro (h | ⟨i, hi, h1, h2⟩)
    · right; exact h
    · left
      simp only [List.getElem_ofFn] at h2
      have : (⟨i, by simpa using hi⟩ : Fin n) = j := Fin.ext (by simpa using h1)
      rw [this] at h2
      exact (Fin.ext h2).symm
  · rintro (h | h)
    · right; exact ⟨j, by simp, by simp, by simp [h]⟩
    · left; exact h

/-- The conditions satisfied by the admissible partial rows. -/
def Good (n x j u : ℕ) (l : List ℕ) : Prop :=
  ∀ i (h : i < l.length), l[i] < n ∧ u.testBit l[i] = false ∧ x.testBit (8 * (j + i) + l[i]) = false

lemma mem_gen {n x : ℕ} : ∀ (k j u : ℕ) (l : List ℕ),
    l ∈ gen n x k j u ↔ l.length = k ∧ l.Nodup ∧ Good n x j u l
  | 0, j, u, l => by
    simp only [gen, List.mem_singleton]
    constructor
    · rintro rfl; simp [Good]
    · rintro ⟨h, -, -⟩; exact List.eq_nil_of_length_eq_zero h
  | k + 1, j, u, l => by
    simp only [gen, List.mem_flatMap, List.mem_range]
    constructor
    · rintro ⟨s, hs, hl⟩
      cases hc : (bit u s || bit x (8 * j + s)) with
      | true => rw [hc] at hl; simp at hl
      | false =>
        rw [hc] at hl
        simp only [cond_false, List.mem_map] at hl
        obtain ⟨l', hl', rfl⟩ := hl
        rw [mem_gen k (j + 1) (u ||| 2 ^ s) l'] at hl'
        obtain ⟨hlen, hnd, hg⟩ := hl'
        simp only [Bool.or_eq_false_iff, bit_eq] at hc
        refine ⟨by simp [hlen], ?_, ?_⟩
        · rw [List.nodup_cons]
          refine ⟨?_, hnd⟩
          intro hmem
          obtain ⟨i, hi, hi'⟩ := List.getElem_of_mem hmem
          have := (hg i hi).2.1
          rw [Nat.testBit_or, Nat.testBit_two_pow, hi'] at this
          simp at this
        · intro i hi
          cases i with
          | zero => simpa using ⟨hs, hc.1, hc.2⟩
          | succ i =>
            have := hg i (by simpa using hi)
            simp only [List.getElem_cons_succ]
            rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
            refine ⟨this.1, this.2.1.1, ?_⟩
            have e : 8 * (j + (i + 1)) = 8 * (j + 1 + i) := by ring
            rw [e]; exact this.2.2
    · rintro ⟨hlen, hnd, hg⟩
      cases l with
      | nil => simp at hlen
      | cons s l' =>
        have h0 := hg 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.add_zero] at h0
        refine ⟨s, h0.1, ?_⟩
        have hc : (bit u s || bit x (8 * j + s)) = false := by
          simp only [bit_eq, h0.2.1, h0.2.2, Bool.or_false]
        rw [hc]
        simp only [cond_false, List.mem_map]
        refine ⟨l', ?_, rfl⟩
        rw [mem_gen k (j + 1) (u ||| 2 ^ s) l']
        rw [List.nodup_cons] at hnd
        refine ⟨by simpa using hlen, hnd.2, ?_⟩
        intro i hi
        have := hg (i + 1) (by simpa using hi)
        simp only [List.getElem_cons_succ] at this
        refine ⟨this.1, ?_, ?_⟩
        · rw [Nat.testBit_or, this.2.1, Nat.testBit_two_pow]
          have : s ≠ l'[i] := fun h => hnd.1 (h ▸ List.getElem_mem hi)
          simp [this]
        · have e : 8 * (j + 1 + i) = 8 * (j + (i + 1)) := by ring
          rw [e]; exact this.2.2

lemma head_of_mem_step {c : Bool} {s : ℕ} {G : List (List ℕ)} {l : List ℕ}
    (h : l ∈ (bif c then [] else G.map (s :: ·))) : l.head? = some s := by
  cases c with
  | true => simp at h
  | false =>
    simp only [cond_false, List.mem_map] at h
    obtain ⟨l', -, rfl⟩ := h
    rfl

lemma nodup_gen {n x : ℕ} : ∀ (k j u : ℕ), (gen n x k j u).Nodup
  | 0, j, u => by simp [gen]
  | k + 1, j, u => by
    simp only [gen]
    rw [List.nodup_flatMap]
    refine ⟨fun s _ => ?_, ?_⟩
    · cases (bit u s || bit x (8 * j + s)) with
      | true => simp
      | false =>
        exact (nodup_gen k (j + 1) _).map (fun a b h => List.cons_injective h)
    · apply List.Nodup.pairwise_of_forall_ne List.nodup_range
      intro s _ s' _ hss' l h1 h2
      have e1 := head_of_mem_step h1
      have e2 := head_of_mem_step h2
      rw [e1] at e2
      exact hss' (Option.some.inj e2)

lemma gen_add {n x : ℕ} : ∀ (k1 k2 j u : ℕ), gen n x (k1 + k2) j u =
    (gen n x k1 j u).flatMap (fun q => (gen n x k2 (j + k1) (u ||| bitsOf q)).map (q ++ ·))
  | 0, k2, j, u => by simp [gen, bitsOf]
  | k1 + 1, k2, j, u => by
    rw [show k1 + 1 + k2 = (k1 + k2) + 1 by omega]
    simp only [gen, List.flatMap_assoc]
    congr 1
    funext s
    cases (bit u s || bit x (8 * j + s)) with
    | true => simp
    | false =>
      simp only [cond_false]
      rw [gen_add k1 k2 (j + 1) (u ||| 2 ^ s), List.map_flatMap, List.flatMap_map]
      congr 1
      funext q
      rw [List.map_map, show j + 1 + k1 = j + (k1 + 1) by omega, bitsOf, Nat.lor_assoc]
      rfl

lemma sum_gen_eq_sum_perm {n : ℕ} (x a : ℕ) (ha : a < n) (hxa : x.testBit a = false)
    (h : List ℕ → ℕ) :
    ((gen n x (n - 1) 1 (2 ^ a)).map (fun l => h (a :: l))).sum =
    ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (∀ j, σ j ∉ dec n x j) ∧ (σ ⟨0, by omega⟩ : ℕ) = a),
      h (List.ofFn (fun j => (σ j : ℕ))) := by
  classical
  set L := (gen n x (n - 1) 1 (2 ^ a)).map (a :: ·) with hLdef
  have hL : (gen n x (n - 1) 1 (2 ^ a)).map (fun l => h (a :: l)) = L.map h := by
    rw [hLdef, List.map_map]; rfl
  have hnd : L.Nodup := (nodup_gen _ _ _).map (fun a b h => List.cons_injective h)
  have hmem : ∀ l, l ∈ L ↔ l.length = n ∧ l.Nodup ∧ Good n x 0 0 l ∧ l[0]? = some a := by
    intro l
    rw [hLdef, List.mem_map]
    constructor
    · rintro ⟨l', hl', rfl⟩
      rw [mem_gen] at hl'
      obtain ⟨hlen, hnd', hg⟩ := hl'
      refine ⟨by simp [hlen]; omega, ?_, ?_, by simp⟩
      · rw [List.nodup_cons]
        refine ⟨fun hm => ?_, hnd'⟩
        obtain ⟨i, hi, hi'⟩ := List.getElem_of_mem hm
        have := (hg i hi).2.1
        rw [Nat.testBit_two_pow, hi'] at this
        simp at this
      · intro i hi
        cases i with
        | zero => simpa using ⟨ha, hxa⟩
        | succ i =>
          have := hg i (by simpa using hi)
          simp only [List.getElem_cons_succ, Nat.zero_testBit]
          refine ⟨this.1, by simp, ?_⟩
          have e : 8 * (0 + (i + 1)) = 8 * (1 + i) := by ring
          rw [e]; exact this.2.2
    · rintro ⟨hlen, hnd', hg, h0⟩
      cases l with
      | nil => simp at h0
      | cons s l' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
        subst h0
        refine ⟨l', ?_, rfl⟩
        rw [List.nodup_cons] at hnd'
        rw [mem_gen]
        refine ⟨by simp at hlen; omega, hnd'.2, ?_⟩
        intro i hi
        have := hg (i + 1) (by simpa using hi)
        simp only [List.getElem_cons_succ] at this
        refine ⟨this.1, ?_, ?_⟩
        · rw [Nat.testBit_two_pow]
          have : s ≠ l'[i] := fun h => hnd'.1 (h ▸ List.getElem_mem hi)
          simp [this]
        · have e : 8 * (1 + i) = 8 * (0 + (i + 1)) := by ring
          rw [e]; exact this.2.2
  set F := univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (∀ j, σ j ∉ dec n x j) ∧ (σ ⟨0, by omega⟩ : ℕ) = a) with hF
  let lst : Equiv.Perm (Fin n) → List ℕ := fun σ => List.ofFn (fun j => (σ j : ℕ))
  have hinj : Function.Injective lst := by
    intro σ τ hστ
    ext j
    have := congrArg (fun l : List ℕ => l[(j : ℕ)]?) hστ
    simpa [lst] using this
  have himg : L.toFinset = F.image lst := by
    ext l
    rw [List.mem_toFinset, hmem, Finset.mem_image]
    constructor
    · rintro ⟨hlen, hnd', hg, h0⟩
      let f : Fin n → Fin n := fun i => ⟨l[(i : ℕ)]'(by omega), (hg i (by omega)).1⟩
      have hfi : Function.Injective f := by
        intro i j hij
        have : l[(i : ℕ)]'(by omega) = l[(j : ℕ)]'(by omega) := congrArg Fin.val hij
        exact Fin.ext ((List.Nodup.getElem_inj_iff hnd').1 this)
      have hfb : Function.Bijective f := Finite.injective_iff_bijective.1 hfi
      refine ⟨Equiv.ofBijective f hfb, ?_, ?_⟩
      · rw [hF, mem_filter]
        refine ⟨mem_univ _, ?_, ?_⟩
        · intro j hj
          simp only [dec, mem_filter, mem_univ, true_and] at hj
          have := (hg j (by omega)).2.2
          simp only [Nat.zero_add] at this
          simp only [Equiv.ofBijective_apply, f] at hj
          rw [this] at hj
          exact absurd hj (by simp)
        · simp only [Equiv.ofBijective_apply, f]
          rw [List.getElem?_eq_getElem (by omega)] at h0
          exact Option.some.inj h0
      · apply List.ext_getElem (by simp [lst, hlen])
        intro i h1 h2
        simp [lst, f]
    · rintro ⟨σ, hσ, rfl⟩
      rw [hF, mem_filter] at hσ
      obtain ⟨-, hc, h0⟩ := hσ
      refine ⟨by simp [lst], ?_, ?_, ?_⟩
      · exact List.nodup_ofFn.2 (fun i j hij => σ.injective (Fin.ext hij))
      · intro i hi
        simp only [lst, List.getElem_ofFn, Nat.zero_testBit, Nat.zero_add]
        refine ⟨(σ _).2, by simp, ?_⟩
        have := hc ⟨i, by simpa [lst] using hi⟩
        simp only [dec, mem_filter, mem_univ, true_and] at this
        simpa using this
      · simp [lst, h0]; omega
  rw [hL, ← List.sum_toFinset _ hnd, himg, Finset.sum_image (fun σ _ τ _ h => hinj h)]

/-! ### The checker -/

lemma childVal_sound {n : ℕ} (hn : n ≤ 8) {x r : ℕ} {T : KT}
    (IH : ∀ z v, (z, r, v) ∈ T.toList → E n (dec n z) r = v) {l : List ℕ} {c v : ℕ}
    (h : childVal n x r T l c = some v) : E n (dec n (x ||| maskL 0 l)) r = v := by
  unfold childVal at h
  cases hc : permOk n c with
  | false => rw [hc] at h; simp at h
  | true =>
    rw [hc] at h
    simp only [cond_true] at h
    cases hf : T.find (canon n (x ||| maskL 0 l) c) with
    | none => rw [hf] at h; simp at h
    | some p =>
      obtain ⟨r', v'⟩ := p
      rw [hf] at h
      simp only at h
      cases hr : Nat.beq r' r with
      | false => rw [hr] at h; simp at h
      | true =>
        rw [hr] at h
        simp only [cond_true, Option.some.injEq] at h
        rw [Nat.beq_eq] at hr
        subst hr h
        rw [← E_canon hn hc]
        exact IH _ _ (KT.find_mem hf)

lemma sumKids_sound {n : ℕ} (hn : n ≤ 8) {x r : ℕ} {T : KT}
    (IH : ∀ z v, (z, r, v) ∈ T.toList → E n (dec n z) r = v) (p : List ℕ) :
    ∀ (ls : List (List ℕ)) (cs : List ℕ) (acc s : ℕ), sumKids n x r T p ls cs acc = some s →
      s = acc + (ls.map (fun l => E n (dec n (x ||| maskL 0 (p ++ l))) r)).sum
  | [], cs, acc, s, h => by simp [sumKids] at h; simp [h]
  | l :: ls, [], acc, s, h => by simp [sumKids] at h
  | l :: ls, c :: cs, acc, s, h => by
    simp only [sumKids] at h
    cases hv : childVal n x r T (p ++ l) c with
    | none => rw [hv] at h; simp at h
    | some v =>
      rw [hv] at h
      simp only at h
      rw [sumKids_sound hn IH p ls cs (acc + v) s h, List.map_cons, List.sum_cons,
        childVal_sound hn IH hv]
      ring

lemma jobCheck_sound {n : ℕ} (hn : n ≤ 8) {T : KT} {J : Job} {r : ℕ} (hr : J.r = r + 1)
    (IH : ∀ z v, (z, r, v) ∈ T.toList → E n (dec n z) r = v) (h : jobCheck n T J = true) :
    J.w = ((gen n J.x (n - J.p.length) J.p.length (bitsOf J.p)).map
      (fun l => E n (dec n (J.x ||| maskL 0 (J.p ++ l))) r)).sum := by
  unfold jobCheck at h
  rw [hr] at h
  simp only at h
  cases hs : sumKids n J.x r T J.p (gen n J.x (n - J.p.length) J.p.length (bitsOf J.p))
    (codesOf J.codes) 0 with
  | none => rw [hs] at h; simp at h
  | some s =>
    rw [hs] at h
    simp only [Nat.beq_eq] at h
    rw [← h, sumKids_sound hn IH _ _ _ _ _ hs, zero_add]

lemma popc_eq (x : ℕ) : ∀ m, popc x m = ∑ s ∈ range m, if x.testBit s then 1 else 0
  | 0 => rfl
  | m + 1 => by
    rw [popc, popc_eq x m, sum_range_succ]
    congr 1
    rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (x >>> m) with h | h <;> simp [h]

lemma card_dec_zero {n : ℕ} (hn : 0 < n) (x : ℕ) : (dec n x ⟨0, hn⟩).card = popc x n := by
  rw [popc_eq, ← Fin.sum_univ_eq_sum_range (fun s => if x.testBit s then 1 else 0) n, dec,
    card_filter]
  simp

lemma sum_flatMap' {α β : Type*} (l : List α) (f : α → List β) (g : β → ℕ) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- Soundness of a certificate: every representative carries the correct value. -/
theorem certSound {n : ℕ} (hn : n ≤ 8) {reps : List Rep} {T : KT} {jobs : List Job}
    (hC : certOk n reps T jobs = true) (hJ : jobsOk n T jobs = true) :
    ∀ R ∈ reps, E n (dec n R.x) R.r = R.v := by
  unfold certOk at hC
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hC
  obtain ⟨⟨hreps, hT⟩, hH⟩ := hC
  have hJ' : ∀ J ∈ jobs, jobCheck n T J = true := List.all_eq_true.1 hJ
  suffices key : ∀ r, ∀ R ∈ reps, R.r = r → E n (dec n R.x) r = R.v by
    intro R hR; exact key _ R hR rfl
  intro r
  induction r with
  | zero =>
    intro R hR hr
    have h := hreps R hR
    unfold repCheck at h
    rw [hr] at h
    simp only [Nat.beq_eq] at h
    rw [E_zero, h]
  | succ r ih =>
    intro R hR hr
    have IH : ∀ z v, (z, r, v) ∈ T.toList → E n (dec n z) r = v := by
      intro z v hz
      rw [hT, List.mem_map] at hz
      obtain ⟨R', hR', he⟩ := hz
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2, h3⟩ := he
      rw [← h1, ← h3]
      exact ih R' hR' h2
    have h := hreps R hR
    unfold repCheck at h
    rw [hr] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, Nat.blt_eq, Nat.ble_eq,
      bit_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hxa, ha⟩, hpop⟩, hd1⟩, hdn⟩, hlen⟩, hv⟩ := h
    have hn0 : 0 < n := by omega
    -- the jobs of `R`
    have hjob : ∀ q w, (q, w) ∈ (gen n R.x (R.d - 1) 1 (2 ^ R.a)).zip R.ws →
        w = ((gen n R.x (n - R.d) R.d (2 ^ R.a ||| bitsOf q)).map
          (fun l => E n (dec n (R.x ||| maskL 0 (R.a :: q ++ l))) r)).sum := by
      intro q w hqw
      have hmem : (R.x, R.r, R.a :: q, w) ∈ jobs.map Job.header := by
        rw [hH, List.mem_flatMap]
        exact ⟨R, hR, List.mem_map.2 ⟨(q, w), hqw, rfl⟩⟩
      obtain ⟨J, hJm, hJh⟩ := List.mem_map.1 hmem
      simp only [Job.header, Prod.mk.injEq] at hJh
      obtain ⟨hx, hJr, hp, hw⟩ := hJh
      have hq : q.length = R.d - 1 := ((mem_gen _ _ _ q).1 (List.of_mem_zip hqw).1).1
      have := jobCheck_sound hn (hJr.trans hr) IH (hJ' J hJm)
      rw [hw, hp, hx] at this
      rw [this]
      have hl : (R.a :: q).length = R.d := by simp [hq]; omega
      rw [hl]
      rfl
    -- the sum over all the rows starting with `a`
    have hsum : R.ws.sum = ((gen n R.x (n - 1) 1 (2 ^ R.a)).map
        (fun l => E n (dec n (R.x ||| maskL 0 (R.a :: l))) r)).sum := by
      have e1 : R.ws.sum = (R.ws.map id).sum := by simp
      rw [e1, show n - 1 = (R.d - 1) + (n - R.d) by omega, gen_add, sum_flatMap']
      symm
      apply sum_zip_eq _ _ _ _ hlen
      intro q w hqw
      rw [hjob q w hqw, show 1 + (R.d - 1) = R.d by omega, List.map_map]
      rfl
    rw [hv, hsum, sum_gen_eq_sum_perm R.x R.a ha hxa
      (fun l => E n (dec n (R.x ||| maskL 0 l)) r)]
    simp only [dec_or_maskL_ofFn hn]
    have hS : (⟨R.a, ha⟩ : Fin n) ∉ dec n R.x ⟨0, hn0⟩ := by
      simp [dec, hxa]
    rw [E_succ_fix (dec n R.x) r ⟨0, hn0⟩ ⟨R.a, ha⟩ hS (by rw [card_dec_zero]; omega)]
    congr 2

/-- The value of `L(n)` certified by a kernel-checked certificate. -/
theorem L_eq_of_certK {n : ℕ} (hn : n ≤ 8) {reps : List Rep} {T : KT} {jobs : List Job}
    (hC : certOk n reps T jobs = true) (hJ : jobsOk n T jobs = true) {v : ℕ}
    (hroot : (reps.map (fun R => (R.x, R.r, R.v))).head? = some (0, n, v)) : L n = v := by
  cases reps with
  | nil => simp at hroot
  | cons R reps =>
    simp only [List.map_cons, List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hroot
    obtain ⟨h1, h2, h3⟩ := hroot
    have := certSound hn hC hJ R (by simp)
    rw [h1, h2, h3] at this
    rw [L_eq_E, ← this]
    congr 1
    funext j
    ext s
    simp [dec]

end STS.LatinKernel
