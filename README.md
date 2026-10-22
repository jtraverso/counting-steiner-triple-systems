# Counting Steiner triple systems in Lean 4: Wilson (1974) and Linial–Luria (2013)

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A complete Lean 4 / Mathlib formalization of two papers on the number of Steiner triple systems
(STS): R. M. Wilson, *Nonisomorphic Steiner triple systems* (1974), and N. Linial and Z. Luria,
*An upper bound on the number of Steiner triple systems* (2013). All statements are in the
namespace `CountingSTS` of `Challenge.lean`.

## Definitions

* `IsSTS B`: every block of `B` has 3 points and any two distinct points lie in exactly one block.
* `N v`: the number of isomorphism classes of STS on `Fin v` (isomorphism = a permutation of the
  points mapping the blocks onto the blocks); `D v`: the number of STS on the fixed set `Fin v`.
* `L n`: the number of Latin squares of order `n`; `D7 v`: the number of STS on `Fin v`
  containing a fixed STS of order 7 on the points `0, …, 6`.
* `vdWPC`: the van der Waerden permanent conjecture (used only as an explicit hypothesis, exactly
  as in Wilson's paper).
* `F n`: the number of proper `(n − 1)`-edge-colourings of `K_n` (ordered 1-factorizations).

## Results

**Wilson (1974).**

| Lean | Statement |
|---|---|
| `N_le_D`, `D_le_factorial_mul_N` | (2.1) `N(v) ≤ D(v) ≤ v! N(v)` |
| `theorem1` | Theorem 1: `N(v) < (e^{-1/2} v)^{v²/6}` for `v ≥ 7` |
| `lemma3` | Lemma 3: `D₇(v) ≥ L(n) D₇(u)³` with `(v+14)/3 ≥ u ≥ v/3 ≥ n ≥ (v−7)/3` |
| `lemma4` | Lemma 4: `D₇(v) ≥ 1` for admissible `v ≥ 15` |
| `lemma5_i`, `lemma5_ii`, `lemma5_iii` | Lemma 5: `L(6) = 6!5!·9408`, `L(7) = 7!6!·16942080`, `L(8) = 8!7!·535281401856` |
| `theorem2`, `theorem2_vdW` | Theorem 2: `N(v) ≥ (e^{-5} v)^{v²/12}`; exponent `v²/6` under `vdWPC` |
| `theorem3`, `theorem3_vdW` | Theorem 3: `N(v) ≥ ((3^{-3/2} e^{-2} − ε) v)^{v²/12}` for large admissible `v` (`v²/6` under `vdWPC`) |
| `theorem4_i`, `theorem4_ii`, `theorem4_iii` | Theorem 4: `N(19) ≥ 2450`, `N(21) ≥ 2160980`, `N(25) ≥ 163929929318400` |

**Linial–Luria (2013).**

| Lean | Statement |
|---|---|
| `theorem_1_1`, `sts_upper_bound_explicit` | Theorem 1.1: `D(n) ≤ ((1 + ε) n / e²)^{n²/6}` for large `n`; explicitly `D(n) ≤ exp((n(n−1)/6)(log n − 2 + 1200/√(n−3)))` for `n ≥ 4` |
| `theorem_1_2`, `oneFactorization_upper_bound_explicit` | Theorem 1.2: `F(n) ≤ ((1 + ε) n / e²)^{n²/2}` for large `n`; explicitly with `n(n−1)/2` and `1200/√(n−2)` for `n ≥ 3` |

Together, Theorem 1.1 and Wilson's lower bounds bracket the number of Steiner triple systems;
Linial–Luria proves the upper half of Wilson's conjecture `STS(n) = ((1 + o(1)) n/e²)^{n²/6}`
(the full conjecture is Keevash's theorem and is not formalized here).

## The finite computations

Wilson's Lemma 5 quotes the numbers of Latin squares of orders 6, 7 and 8 from the literature
(Fisher–Yates; Wells 1967). Here they are proved: `RequestProject/LatinKernel.lean` is a checker
written with natural-number bit operations, proved sound in `LatinKernelSound.lean` (with a
row-symmetry reduction in `LatinRowSym.lean`); untrusted certificates (`LatinData*.lean`,
generated externally) are checked by the Lean kernel with `decide +kernel`, split into one
theorem per job (`LatinJobs*.lean`) and combined in `LatinCert*.lean`. Explicit Steiner triple
systems of small orders used in Lemma 4 are checked the same way (`STSKernel.lean`,
`Explicit.lean`). No `native_decide` is used anywhere; the only axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the audited statements. It imports only
  Mathlib.
- [`Solution.lean`](Solution.lean) and [`RequestProject/`](RequestProject): the proofs
  (`RequestProject/LL/` for Linial–Luria).
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## Sources

* R. M. Wilson, *Nonisomorphic Steiner triple systems*, Math. Z. 135 (1974) 303–313,
  doi:10.1007/BF01215371.
* N. Linial, Z. Luria, *An upper bound on the number of Steiner triple systems*, Random Structures
  Algorithms 43 (2013) 399–406, doi:10.1002/rsa.20487.
* J. Doyen, R. M. Wilson, *Embeddings of Steiner triple systems*, Discrete Math. 5 (1973) 229–239,
  doi:10.1016/0012-365X(73)90139-8.
* M. B. Wells, *The number of Latin squares of order eight*, J. Combin. Theory 3 (1967) 98–99,
  doi:10.1016/S0021-9800(67)80021-8.

## Authorship and use of AI

The author chose the papers and directed the work. The formalization was produced by Harmonic's
Aristotle from the papers (Wilson first, then Linial–Luria on top of it), with the finite
computations first checked by `native_decide`; at the author's request Aristotle then replaced
every `native_decide` by kernel-checked certificates. Claude (Claude Code) audited the statements,
ported the project to the pinned toolchain, split the order-8 certificate into per-job kernel
checks, rebuilt everything locally and prepared this package. Lean checks everything
mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```

The kernel checks of the Latin-square certificates take several minutes and a few GB of memory.
