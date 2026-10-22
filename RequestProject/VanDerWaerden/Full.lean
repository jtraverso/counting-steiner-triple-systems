/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LowerBound
public import RequestProject.VanDerWaerden.Theorem

/-!
# Unconditional versions of Theorems 2 and 3

Since the van der Waerden permanent conjecture is a theorem (`STS.van_der_waerden`), the
conditional lower bounds `STS.theorem2_vdW` and `STS.theorem3_vdW` hold unconditionally.

* `STS.theorem2_full` : `N(v) ≥ (e^{-5} v)^{v²/6}` for admissible `v`.
* `STS.theorem3_full` : `N(v) ≥ ((3^{-3/2} e^{-2} - ε) v)^{v²/6}` for all large admissible `v`.
-/

@[expose] public section

open Filter

namespace STS

/-- **Theorem 2**, second part, unconditionally: `N(v) ≥ (e^{-5} v)^{v²/6}`. -/
theorem theorem2_full (v : ℕ) (hv : Admissible v) :
    (Real.exp (-5) * v) ^ ((v : ℝ) ^ 2 / 6) ≤ N v :=
  theorem2_vdW van_der_waerden v hv

/-- **Theorem 3**, second part (inequality (1.2)), unconditionally: for any `ε > 0` (small enough
that the base is positive) and all sufficiently large admissible `v`,
`N(v) ≥ ((3^{-3/2} e^{-2} - ε) v)^{v²/6}`. -/
theorem theorem3_full (ε : ℝ) (hε : 0 < ε) (hε' : ε < (3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2)) :
    ∀ᶠ v : ℕ in Filter.atTop, Admissible v →
      (((3 : ℝ) ^ (-3 / 2 : ℝ) * Real.exp (-2) - ε) * v) ^ ((v : ℝ) ^ 2 / 6) ≤ N v :=
  theorem3_vdW van_der_waerden ε hε hε'

end STS
