/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LatinKernelSound
public import RequestProject.LatinCert6
public import RequestProject.LatinCert7
public import RequestProject.LatinCert8

/-!
# Lemma 5: the numbers of Latin squares of orders 6, 7 and 8

The paper quotes these values from the literature; here they are obtained from a verified
certificate checker (`STS.LatinKernel.L_eq_of_certK`), the certificates being checked by the
kernel (`decide +kernel`) in the files `RequestProject/LatinJobs*.lean` and
`RequestProject/LatinCert*.lean`.
-/

@[expose] public section

namespace STS

open LatinKernel

/-- **Lemma 5 (i).** `L(6) = 6! 5! · 9408`. -/
theorem lemma5_i : L 6 = Nat.factorial 6 * Nat.factorial 5 * 9408 := by
  rw [L_eq_of_certK (by norm_num) cert6_ok jobs6_ok root6]
  norm_num [Nat.factorial]

/-- **Lemma 5 (ii).** `L(7) = 7! 6! · 16942080`. -/
theorem lemma5_ii : L 7 = Nat.factorial 7 * Nat.factorial 6 * 16942080 := by
  rw [L_eq_of_certK (by norm_num) cert7_ok jobs7_ok root7]
  norm_num [Nat.factorial]

/-- **Lemma 5 (iii).** `L(8) = 8! 7! · 535281401856`. -/
theorem lemma5_iii : L 8 = Nat.factorial 8 * Nat.factorial 7 * 535281401856 := by
  rw [L_eq_of_certK (by norm_num) cert8_ok jobs8_ok root8]
  norm_num [Nat.factorial]

end STS
