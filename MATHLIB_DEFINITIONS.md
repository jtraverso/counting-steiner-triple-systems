# Mathlib definitions used in Challenge.lean

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib.

## Finset.card

`Mathlib/Data/Finset/Card.lean`, line 47:

```lean
/-- `s.card` is the number of elements of `s`, aka its cardinality.

The notation `#s` can be accessed in the `Finset` locale. -/
def card (s : Finset α) : ℕ :=
  Multiset.card s.1
```

## Finset.image

`Mathlib/Data/Finset/Image.lean`, line 279:

```lean
/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset
```

## Nat.card

`Mathlib/SetTheory/Cardinal/Finite.lean`, line 41:

```lean
/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ :=
  toNat (mk α)
```

## Function.Bijective

`Mathlib/Logic/Function/Defs.lean`, line 163:

```lean
/-- A function is called bijective if it is both injective and surjective. -/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f
```

## Equiv.Perm

`Mathlib/Logic/Equiv/Defs.lean`, line 96:

```lean
/-- `Perm α` is the type of bijections from `α` to itself. -/
abbrev Equiv.Perm (α : Sort*) :=
  Equiv α α
```

## Nat.factorial

`Mathlib/Data/Nat/Factorial/Basic.lean`, line 37:

```lean
/-- `Nat.factorial n` is the factorial of `n`. -/
@[wikidata Q120976]
def factorial : ℕ → ℕ
  | 0 => 1
  | succ n => succ n * factorial n
```

## Matrix.permanent

`Mathlib/LinearAlgebra/Matrix/Permanent.lean`, line 32:

```lean
/-- The permanent of a square matrix defined as a sum over all permutations. This is analogous to
the determinant but without alternating signs. -/
def permanent (M : Matrix n n R) : R := ∑ σ : Perm n, ∏ i, M (σ i) i
```

## doublyStochastic

`Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean`, line 42:

```lean
/--
A square matrix is doubly stochastic iff all entries are nonnegative, and left or right
multiplication by the vector of all 1s gives the vector of all 1s.
-/
def doublyStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] :
    Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_, ?_⟩
    next => rw [← mulVec_mulVec, hN.2.1, hM.2.1]
    next => rw [← vecMul_vecMul, hM.2.2, hN.2.2]
  one_mem' := by simp [zero_le_one_elem]
```

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 95:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## SimpleGraph.lineGraph

`Mathlib/Combinatorics/SimpleGraph/LineGraph.lean`, line 34:

```lean
/--
The line graph of a simple graph `G` has its vertex set as the edges of `G`, and two vertices of
the line graph are adjacent if the corresponding edges share a vertex in `G`.
-/
def lineGraph : SimpleGraph G.edgeSet where
  Adj e₁ e₂ := e₁ ≠ e₂ ∧ (e₁ ∩ e₂ : Set V).Nonempty
  symm.symm e₁ e₂ hadj := by rwa [ne_comm, Set.inter_comm]
```

## SimpleGraph.Coloring

`Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, line 74:

```lean
/-- An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
abbrev Coloring (α : Type v) := G →g completeGraph α
```

## Real.exp

`Mathlib/Analysis/Complex/Exponential.lean`, line 80:

```lean
/-- The real exponential function, defined as the real part of the complex exponential -/
@[pp_nodot, wikidata Q168698]
nonrec def exp (x : ℝ) : ℝ :=
  (exp x).re
```

## Real.rpow

`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`, line 35:

```lean
/-- The real power function `x ^ y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`, one sets `0 ^ 0=1` and `0 ^ y=0` for
`y ≠ 0`. For `x < 0`, the definition is somewhat arbitrary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (π y)`. -/
noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re
```

## Filter.atTop

`Mathlib/Order/Filter/AtTopBot/Defs.lean`, line 39:

```lean
def atTop [Preorder α] : Filter α :=
  ⨅ a, 𝓟 (Ici a)
```

## Filter.Eventually

`Mathlib/Order/Filter/Defs.lean`, line 281:

```lean
/-- `f.Eventually p` or `∀ᶠ x in f, p x` mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in atTop, p x`
means that `p` holds true for sufficiently large `x`. -/
protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f
```
