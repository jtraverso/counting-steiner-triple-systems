/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Basic

/-!
# The construction of Lemma 3

Let `W` be a finite set and `n` a natural number. Put `Y = W ⊕ Fin n` and
`X = W ⊕ (Fin 3 × Fin n)`, so that `X` is the disjoint union of `W` and three copies
`Zᵢ = {i} × Fin n` of `Fin n`, and `ιᵢ : Y → X` identifies `Y` with `W ∪ Zᵢ`.

Given STS's `Bᵢ` on `Y` (`i = 0, 1, 2`) all containing a fixed family `G` which covers every
pair of points of `W` by a block inside `W`, and a Latin square `l` of order `n`, the family

`Φ(B, l) = ι₀(B₀) ∪ ι₁(B₁) ∪ ι₂(B₂) ∪ {{(0,x), (1,y), (2, l(x,y))}}`

is an STS on `X` containing `ι₀(G)`, and `(B, l) ↦ Φ(B, l)` is injective. Hence the number of
STS's on `X` containing `ι₀(G)` is at least `L(n) · (number of STS's on Y containing G)³`.
-/

@[expose] public section

open Finset

namespace STS

/-- The number of STS's on `α` containing the family `B₀`. -/
noncomputable def DSub (α : Type*) [DecidableEq α] (B₀ : Finset (Finset α)) : ℕ :=
  Nat.card {B : Finset (Finset α) // IsSTS B ∧ B₀ ⊆ B}

/-- `DSub` is invariant under relabelling the points. -/
lemma DSub_equiv {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (B₀ : Finset (Finset α)) : DSub β (mapBlocks e B₀) = DSub α B₀ := by
  unfold DSub
  refine Nat.card_congr ⟨fun B => ⟨mapBlocks e.symm B.1, isSTS_mapBlocks_equiv e.symm B.2.1, ?_⟩,
    fun B => ⟨mapBlocks e B.1, isSTS_mapBlocks_equiv e B.2.1, mapBlocks_subset_mapBlocks B.2.2⟩,
    ?_, ?_⟩
  · have := mapBlocks_subset_mapBlocks (f := e.symm) B.2.2
    rwa [mapBlocks_symm_mapBlocks] at this
  · intro B; apply Subtype.ext; simp only
    have := mapBlocks_symm_mapBlocks e.symm B.1
    simpa using this
  · intro B; apply Subtype.ext; simp only; exact mapBlocks_symm_mapBlocks e B.1

namespace Construction

variable {W : Type*} [DecidableEq W] {n : ℕ}

/-- The embedding `ιᵢ : W ⊕ Fin n → W ⊕ (Fin 3 × Fin n)`. -/
def ι (i : Fin 3) : W ⊕ Fin n → W ⊕ (Fin 3 × Fin n) := Sum.map id (fun b => (i, b))

lemma ι_injective (i : Fin 3) : Function.Injective (ι (W := W) (n := n) i) := by
  intro x y h
  cases x <;> cases y <;> simp_all [ι]

/-- The block of the Latin square `l` at the cell `(x, y)`. -/
def T (l : Fin n → Fin n → Fin n) (xy : Fin n × Fin n) : Finset (W ⊕ (Fin 3 × Fin n)) :=
  {Sum.inr (0, xy.1), Sum.inr (1, xy.2), Sum.inr (2, l xy.1 xy.2)}

/-- The blocks coming from the Latin square `l`. -/
def latinBlocks (l : Fin n → Fin n → Fin n) : Finset (Finset (W ⊕ (Fin 3 × Fin n))) :=
  univ.image (T l)

/-- The family `Φ(B, l)`. -/
def Φ (B : Fin 3 → Finset (Finset (W ⊕ Fin n))) (l : Fin n → Fin n → Fin n) :
    Finset (Finset (W ⊕ (Fin 3 × Fin n))) :=
  univ.biUnion (fun i => mapBlocks (ι i) (B i)) ∪ latinBlocks l

lemma inl_notMem_T (l : Fin n → Fin n → Fin n) (xy : Fin n × Fin n) (a : W) :
    (Sum.inl a : W ⊕ (Fin 3 × Fin n)) ∉ T l xy := by
  simp [T]

lemma inr_mem_T (l : Fin n → Fin n → Fin n) (xy : Fin n × Fin n) (i : Fin 3) (b : Fin n) :
    (Sum.inr (i, b) : W ⊕ (Fin 3 × Fin n)) ∈ T l xy ↔
      (i = 0 ∧ b = xy.1) ∨ (i = 1 ∧ b = xy.2) ∨ (i = 2 ∧ b = l xy.1 xy.2) := by
  simp [T]

lemma card_T (l : Fin n → Fin n → Fin n) (xy : Fin n × Fin n) :
    (T (W := W) l xy).card = 3 := by
  simp [T]

lemma inl_mem_ι (A : Finset (W ⊕ Fin n)) (j : Fin 3) (a : W) :
    (Sum.inl a : W ⊕ (Fin 3 × Fin n)) ∈ A.image (ι j) ↔ Sum.inl a ∈ A := by
  constructor
  · intro h
    obtain ⟨z, hz, hze⟩ := mem_image.1 h
    cases z with
    | inl c => simp only [ι, Sum.map_inl, id, Sum.inl.injEq] at hze; rwa [← hze]
    | inr c => simp [ι] at hze
  · intro h; exact mem_image.2 ⟨_, h, rfl⟩

lemma inr_mem_ι (A : Finset (W ⊕ Fin n)) (j i : Fin 3) (b : Fin n) :
    (Sum.inr (i, b) : W ⊕ (Fin 3 × Fin n)) ∈ A.image (ι j) ↔ i = j ∧ Sum.inr b ∈ A := by
  constructor
  · intro h
    obtain ⟨z, hz, hze⟩ := mem_image.1 h
    cases z with
    | inl c => simp [ι] at hze
    | inr c =>
      simp only [ι, Sum.map_inr, Sum.inr.injEq, Prod.mk.injEq] at hze
      obtain ⟨rfl, rfl⟩ := hze
      exact ⟨rfl, hz⟩
  · rintro ⟨rfl, h⟩; exact mem_image.2 ⟨_, h, rfl⟩

/-- Images of a family of points of `W` under the different `ιᵢ` agree. -/
lemma image_ι_eq_of_left (A : Finset (W ⊕ Fin n)) (hA : ∀ z ∈ A, z.isLeft = true)
    (i j : Fin 3) : A.image (ι i) = A.image (ι j) := by
  apply image_congr
  intro z hz
  have := hA z hz
  cases z with
  | inl c => rfl
  | inr c => simp at this

/-- A latin cell is determined by any two of its three entries. -/
lemma latin_cover {l : Fin n → Fin n → Fin n} (hl : IsLatin l) (i j : Fin 3) (b b' : Fin n)
    (hij : i ≠ j) : ∃! xy : Fin n × Fin n,
      (Sum.inr (i, b) : W ⊕ (Fin 3 × Fin n)) ∈ T (W := W) l xy ∧
        (Sum.inr (j, b') : W ⊕ (Fin 3 × Fin n)) ∈ T (W := W) l xy := by
  simp only [inr_mem_T]
  obtain ⟨hrow, hcol⟩ := hl
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · refine ⟨(b, b'), ⟨rfl, rfl⟩, ?_⟩
    rintro ⟨x', y'⟩ ⟨h1, h2⟩
    simp only at h1 h2; subst h1; subst h2; rfl
  · obtain ⟨y, hy⟩ := (hrow b).2 b'
    refine ⟨(b, y), ⟨rfl, hy.symm⟩, ?_⟩
    rintro ⟨x', y'⟩ ⟨h1, h2⟩
    simp only at h1 h2; subst h1
    exact Prod.ext rfl ((hrow b).1 (h2.symm.trans hy.symm))
  · refine ⟨(b', b), ⟨rfl, rfl⟩, ?_⟩
    rintro ⟨x', y'⟩ ⟨h1, h2⟩
    simp only at h1 h2; subst h1; subst h2; rfl
  · obtain ⟨x, hx⟩ := (hcol b).2 b'
    refine ⟨(x, b), ⟨rfl, hx.symm⟩, ?_⟩
    rintro ⟨x', y'⟩ ⟨h1, h2⟩
    simp only at h1 h2; subst h1
    exact Prod.ext ((hcol b).1 (h2.symm.trans hx.symm)) rfl
  · obtain ⟨y, hy⟩ := (hrow b').2 b
    refine ⟨(b', y), ⟨hy.symm, rfl⟩, ?_⟩
    rintro ⟨x', y'⟩ ⟨h1, h2⟩
    simp only at h1 h2; subst h2
    exact Prod.ext rfl ((hrow b').1 (h1.symm.trans hy.symm))
  · obtain ⟨x, hx⟩ := (hcol b').2 b
    refine ⟨(x, b'), ⟨hx.symm, rfl⟩, ?_⟩
    rintro ⟨x', y'⟩ ⟨h1, h2⟩
    simp only at h1 h2; subst h2
    exact Prod.ext ((hcol b').1 (h1.symm.trans hx.symm)) rfl

lemma mem_Φ {B : Fin 3 → Finset (Finset (W ⊕ Fin n))} {l : Fin n → Fin n → Fin n}
    {C : Finset (W ⊕ (Fin 3 × Fin n))} :
    C ∈ Φ B l ↔ (∃ j, ∃ A ∈ B j, C = A.image (ι j)) ∨ ∃ xy, C = T l xy := by
  simp only [Φ, mem_union, mem_biUnion, mem_univ, true_and, mapBlocks, mem_image, latinBlocks]
  constructor
  · rintro (⟨j, A, hA, rfl⟩ | ⟨xy, rfl⟩)
    · exact Or.inl ⟨j, A, hA, rfl⟩
    · exact Or.inr ⟨xy, rfl⟩
  · rintro (⟨j, A, hA, rfl⟩ | ⟨xy, rfl⟩)
    · exact Or.inl ⟨j, A, hA, rfl⟩
    · exact Or.inr ⟨xy, rfl⟩

/-- The hypothesis on `G`: every pair of points of `W` is covered by a block of `G` inside `W`. -/
def CoversW (G : Finset (Finset (W ⊕ Fin n))) : Prop :=
  ∀ a a' : W, a ≠ a' → ∃ A ∈ G, Sum.inl a ∈ A ∧ Sum.inl a' ∈ A ∧ ∀ z ∈ A, z.isLeft = true

variable {G : Finset (Finset (W ⊕ Fin n))}

/-- In an STS containing `G`, the block through two points of `W` is the block of `G`. -/
lemma block_of_W {B : Finset (Finset (W ⊕ Fin n))} (hB : IsSTS B ∧ G ⊆ B) (hG : CoversW G)
    {a a' : W} (haa : a ≠ a') {A : Finset (W ⊕ Fin n)} (hA : A ∈ B) (ha : Sum.inl a ∈ A)
    (ha' : Sum.inl a' ∈ A) : A ∈ G ∧ ∀ z ∈ A, z.isLeft = true := by
  obtain ⟨AG, hAG, h1, h2, h3⟩ := hG a a' haa
  obtain ⟨C, _, hC⟩ := hB.1.2 (Sum.inl a) (Sum.inl a') (by simpa using haa)
  have e1 := hC A ⟨hA, ha, ha'⟩
  have e2 := hC AG ⟨hB.2 hAG, h1, h2⟩
  rw [e1, ← e2]
  exact ⟨hAG, h3⟩

theorem isSTS_Φ {B : Fin 3 → Finset (Finset (W ⊕ Fin n))} (hB : ∀ i, IsSTS (B i) ∧ G ⊆ B i)
    (hG : CoversW G) {l : Fin n → Fin n → Fin n} (hl : IsLatin l) : IsSTS (Φ B l) := by
  refine ⟨?_, ?_⟩
  · intro C hC
    rcases mem_Φ.1 hC with ⟨j, A, hA, rfl⟩ | ⟨xy, rfl⟩
    · rw [card_image_of_injective _ (ι_injective j)]; exact (hB j).1.1 A hA
    · exact card_T l xy
  -- the pair condition
  have key : ∀ p q : W ⊕ (Fin 3 × Fin n), p ≠ q →
      ∃! C, C ∈ Φ B l ∧ p ∈ C ∧ q ∈ C := by
    intro p q hpq
    rcases p with a | ⟨i, b⟩ <;> rcases q with a' | ⟨i', b'⟩
    · -- two points of W
      have haa : a ≠ a' := fun h => hpq (by rw [h])
      obtain ⟨AG, hAG, h1, h2, h3⟩ := hG a a' haa
      refine ⟨AG.image (ι 0), ⟨mem_Φ.2 (Or.inl ⟨0, AG, (hB 0).2 hAG, rfl⟩),
        (inl_mem_ι _ _ _).2 h1, (inl_mem_ι _ _ _).2 h2⟩, ?_⟩
      rintro C ⟨hC, hp, hq⟩
      rcases mem_Φ.1 hC with ⟨j, A, hA, rfl⟩ | ⟨xy, rfl⟩
      · rw [inl_mem_ι] at hp hq
        obtain ⟨hAG', hleft⟩ := block_of_W (hB j) hG haa hA hp hq
        have : A = AG := by
          obtain ⟨C, _, hC⟩ := (hB j).1.2 (Sum.inl a) (Sum.inl a') (by simpa using haa)
          rw [hC A ⟨hA, hp, hq⟩, hC AG ⟨(hB j).2 hAG, h1, h2⟩]
        subst this
        exact image_ι_eq_of_left A hleft j 0
      · exact absurd hp (inl_notMem_T l xy a)
    · -- a point of W and a point of Z_i'
      obtain ⟨A, ⟨hA, h1, h2⟩, hAu⟩ := (hB i').1.2 (Sum.inl a) (Sum.inr b') (by simp)
      refine ⟨A.image (ι i'), ⟨mem_Φ.2 (Or.inl ⟨i', A, hA, rfl⟩),
        (inl_mem_ι _ _ _).2 h1, (inr_mem_ι _ _ _ _).2 ⟨rfl, h2⟩⟩, ?_⟩
      rintro C ⟨hC, hp, hq⟩
      rcases mem_Φ.1 hC with ⟨j, A', hA', rfl⟩ | ⟨xy, rfl⟩
      · rw [inl_mem_ι] at hp
        rw [inr_mem_ι] at hq
        obtain ⟨rfl, hq⟩ := hq
        rw [hAu A' ⟨hA', hp, hq⟩]
      · exact absurd hp (inl_notMem_T l xy a)
    · -- a point of Z_i and a point of W
      obtain ⟨A, ⟨hA, h1, h2⟩, hAu⟩ := (hB i).1.2 (Sum.inr b) (Sum.inl a') (by simp)
      refine ⟨A.image (ι i), ⟨mem_Φ.2 (Or.inl ⟨i, A, hA, rfl⟩),
        (inr_mem_ι _ _ _ _).2 ⟨rfl, h1⟩, (inl_mem_ι _ _ _).2 h2⟩, ?_⟩
      rintro C ⟨hC, hp, hq⟩
      rcases mem_Φ.1 hC with ⟨j, A', hA', rfl⟩ | ⟨xy, rfl⟩
      · rw [inl_mem_ι] at hq
        rw [inr_mem_ι] at hp
        obtain ⟨rfl, hp⟩ := hp
        rw [hAu A' ⟨hA', hp, hq⟩]
      · exact absurd hq (inl_notMem_T l xy a')
    · by_cases hii : i = i'
      · -- two points of the same Z_i
        subst hii
        have hbb : b ≠ b' := fun h => hpq (by rw [h])
        obtain ⟨A, ⟨hA, h1, h2⟩, hAu⟩ := (hB i).1.2 (Sum.inr b) (Sum.inr b') (by simpa using hbb)
        refine ⟨A.image (ι i), ⟨mem_Φ.2 (Or.inl ⟨i, A, hA, rfl⟩),
          (inr_mem_ι _ _ _ _).2 ⟨rfl, h1⟩, (inr_mem_ι _ _ _ _).2 ⟨rfl, h2⟩⟩, ?_⟩
        rintro C ⟨hC, hp, hq⟩
        rcases mem_Φ.1 hC with ⟨j, A', hA', rfl⟩ | ⟨xy, rfl⟩
        · rw [inr_mem_ι] at hp hq
          obtain ⟨rfl, hp⟩ := hp
          rw [hAu A' ⟨hA', hp, hq.2⟩]
        · exfalso
          rw [inr_mem_T] at hp hq
          fin_cases i <;> simp at hp hq <;> exact hbb (hp.trans hq.symm)
      · -- points of two different Z's
        obtain ⟨xy, ⟨h1, h2⟩, hxyu⟩ := latin_cover (W := W) hl i i' b b' hii
        refine ⟨T l xy, ⟨mem_Φ.2 (Or.inr ⟨xy, rfl⟩), h1, h2⟩, ?_⟩
        rintro C ⟨hC, hp, hq⟩
        rcases mem_Φ.1 hC with ⟨j, A', hA', rfl⟩ | ⟨xy', rfl⟩
        · rw [inr_mem_ι] at hp hq
          exact absurd (hp.1.trans hq.1.symm) hii
        · rw [hxyu xy' ⟨hp, hq⟩]
  intro p q hpq
  exact key p q hpq

lemma ι_G_subset_Φ {B : Fin 3 → Finset (Finset (W ⊕ Fin n))} (hB : ∀ i, IsSTS (B i) ∧ G ⊆ B i)
    (l : Fin n → Fin n → Fin n) : mapBlocks (ι 0) G ⊆ Φ B l := by
  intro C hC
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
  exact mem_Φ.2 (Or.inl ⟨0, A, (hB 0).2 hA, rfl⟩)

/-- The systems `Bᵢ` can be recovered from `Φ(B, l)`. -/
lemma mem_B_iff {B : Fin 3 → Finset (Finset (W ⊕ Fin n))} (hB : ∀ i, IsSTS (B i) ∧ G ⊆ B i)
    (hG : CoversW G) {l : Fin n → Fin n → Fin n} (i : Fin 3) (A : Finset (W ⊕ Fin n)) :
    A ∈ B i ↔ A.image (ι i) ∈ Φ B l := by
  constructor
  · intro hA; exact mem_Φ.2 (Or.inl ⟨i, A, hA, rfl⟩)
  · intro h
    rcases mem_Φ.1 h with ⟨j, A', hA', he⟩ | ⟨xy, he⟩
    · by_cases hij : i = j
      · subst hij
        rw [image_injective (ι_injective i) he]; exact hA'
      · -- then `A ⊆ W`
        have hleft : ∀ z ∈ A, z.isLeft = true := by
          intro z hz
          cases z with
          | inl c => rfl
          | inr c =>
            have : (Sum.inr (i, c) : W ⊕ (Fin 3 × Fin n)) ∈ A'.image (ι j) := by
              rw [← he]; exact (inr_mem_ι _ _ _ _).2 ⟨rfl, hz⟩
            rw [inr_mem_ι] at this
            exact absurd this.1 hij
        have hA'A : A' = A := by
          rw [image_ι_eq_of_left A hleft i j] at he
          exact (image_injective (ι_injective j) he).symm
        subst hA'A
        -- `A'` is a block of `B j` inside `W`; it has two points
        have h3 := (hB j).1.1 A' hA'
        obtain ⟨z₁, hz₁, z₂, hz₂, hz⟩ := Finset.one_lt_card.1 (by omega : 1 < A'.card)
        have hl1 := hleft z₁ hz₁
        have hl2 := hleft z₂ hz₂
        cases z₁ with
        | inr c => simp at hl1
        | inl a =>
          cases z₂ with
          | inr c => simp at hl2
          | inl a' =>
            have haa : a ≠ a' := fun h => hz (by rw [h])
            exact (hB i).2 (block_of_W (hB j) hG haa hA' hz₁ hz₂).1
    · exfalso
      have h0 : (Sum.inr (0, xy.1) : W ⊕ (Fin 3 × Fin n)) ∈ A.image (ι i) := by
        rw [he]; simp [T]
      have h1 : (Sum.inr (1, xy.2) : W ⊕ (Fin 3 × Fin n)) ∈ A.image (ι i) := by
        rw [he]; simp [T]
      rw [inr_mem_ι] at h0 h1
      exact absurd (h0.1.trans h1.1.symm) (by decide)

theorem Φ_injective {B B' : Fin 3 → Finset (Finset (W ⊕ Fin n))}
    (hB : ∀ i, IsSTS (B i) ∧ G ⊆ B i) (hB' : ∀ i, IsSTS (B' i) ∧ G ⊆ B' i) (hG : CoversW G)
    {l l' : Fin n → Fin n → Fin n} (h : Φ B l = Φ B' l') : B = B' ∧ l = l' := by
  refine ⟨?_, ?_⟩
  · funext i
    ext A
    rw [mem_B_iff hB hG (l := l), mem_B_iff hB' hG (l := l'), h]
  · funext x y
    have hT : T l (x, y) ∈ Φ B' l' := by
      rw [← h]; exact mem_Φ.2 (Or.inr ⟨(x, y), rfl⟩)
    rcases mem_Φ.1 hT with ⟨j, A', hA', he⟩ | ⟨xy, he⟩
    · exfalso
      have h0 : (Sum.inr (0, x) : W ⊕ (Fin 3 × Fin n)) ∈ A'.image (ι j) := by
        rw [← he]; simp [T]
      have h1 : (Sum.inr (1, y) : W ⊕ (Fin 3 × Fin n)) ∈ A'.image (ι j) := by
        rw [← he]; simp [T]
      rw [inr_mem_ι] at h0 h1
      exact absurd (h0.1.trans h1.1.symm) (by decide)
    · have h0 : (Sum.inr (0, x) : W ⊕ (Fin 3 × Fin n)) ∈ T l' xy := by rw [← he]; simp [T]
      have h1 : (Sum.inr (1, y) : W ⊕ (Fin 3 × Fin n)) ∈ T l' xy := by rw [← he]; simp [T]
      have h2 : (Sum.inr (2, l x y) : W ⊕ (Fin 3 × Fin n)) ∈ T l' xy := by rw [← he]; simp [T]
      rw [inr_mem_T] at h0 h1 h2
      simp at h0 h1 h2
      rw [h2, h0, h1]

/-- The counting consequence of the construction. -/
theorem card_le [Fintype W] (hG : CoversW G) :
    L n * DSub (W ⊕ Fin n) G ^ 3 ≤ DSub (W ⊕ (Fin 3 × Fin n)) (mapBlocks (ι 0) G) := by
  classical
  let S := {B : Finset (Finset (W ⊕ Fin n)) // IsSTS B ∧ G ⊆ B}
  let F : {l : Fin n → Fin n → Fin n // IsLatin l} × (Fin 3 → S) →
      {C : Finset (Finset (W ⊕ (Fin 3 × Fin n))) // IsSTS C ∧ mapBlocks (ι 0) G ⊆ C} :=
    fun p => ⟨Φ (fun i => (p.2 i).1) p.1.1, isSTS_Φ (fun i => (p.2 i).2) hG p.1.2,
      ι_G_subset_Φ (fun i => (p.2 i).2) _⟩
  have hF : Function.Injective F := by
    rintro ⟨l, B⟩ ⟨l', B'⟩ h
    have h' := congrArg Subtype.val h
    obtain ⟨h1, h2⟩ := Φ_injective (fun i => (B i).2) (fun i => (B' i).2) hG h'
    have hl : l = l' := Subtype.ext h2
    have hB : B = B' := funext (fun i => Subtype.ext (congrFun h1 i))
    rw [hl, hB]
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at this
  exact this

end Construction

end STS
