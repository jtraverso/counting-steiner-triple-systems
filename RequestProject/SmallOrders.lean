/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Lemma5
public import RequestProject.Theorem4
public import RequestProject.Theorem4i

/-!
# Section 5 of the paper: triple systems with `v ≤ 25`

This file only collects the results of Section 5, which are proved in the following files:

* `STS.lemma5_i`, `STS.lemma5_ii`, `STS.lemma5_iii` (`RequestProject/Lemma5.lean`) : Lemma 5,
  the values of `L(6)`, `L(7)`, `L(8)`.
* `STS.IsFlat`, `STS.lemma6` (`RequestProject/Flats.lean`) : flats and Lemma 6.
* `STS.theorem4_i` (`RequestProject/Theorem4i.lean`), `STS.theorem4_ii`, `STS.theorem4_iii`
  (`RequestProject/Theorem4.lean`) : Theorem 4.
-/

@[expose] public section

namespace STS

example : L 6 = Nat.factorial 6 * Nat.factorial 5 * 9408 := lemma5_i
example : L 7 = Nat.factorial 7 * Nat.factorial 6 * 16942080 := lemma5_ii
example : L 8 = Nat.factorial 8 * Nat.factorial 7 * 535281401856 := lemma5_iii
example : 2450 ≤ N 19 := theorem4_i
example : 2160980 ≤ N 21 := theorem4_ii
example : 163929929318400 ≤ N 25 := theorem4_iii

end STS
