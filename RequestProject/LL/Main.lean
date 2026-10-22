/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LL.STSMain
public import RequestProject.LL.OFMain

/-!
# N. Linial, Z. Luria, *An upper bound on the number of Steiner triple systems*

Index of the formalization (namespace `LinialLuria`).

* **Theorem 1.1** `theorem_1_1` (`RequestProject/LL/STSMain.lean`):
  `STS(n) ≤ ((1 + o(1)) n / e²)^{n²/6}`, where `STS(n) = STS.D n` is the number of Steiner
  triple systems on `Fin n`; explicit form `sts_upper_bound_explicit`.
* **Theorem 1.2** `theorem_1_2` (`RequestProject/LL/OFMain.lean`):
  `F(n) ≤ ((1 + o(1)) n / e²)^{n²/2}`, where `F(n)` is the number of 1-factorizations of `K_n`;
  explicit form `oneFactorization_upper_bound_explicit`.
* **Conjecture 1.3** is only stated (`Conjecture_1_3_STS`, `Conjecture_1_3_F`); it is open.

The proofs follow the entropy method of the paper:

* the chain rule `H(X) = ∑ H(X_e | X_{e'}, e' ≺ e) ≤ ∑ E[log N_e]` is replaced by its purely
  combinatorial content, `chain_bound` (`RequestProject/LL/Chain.lean`);
* the random vertex order `≪` and the random orders of the stars `E_v` are realised by uniform
  random labels (`RequestProject/LL/Order.lean`), so that the conditional probabilities of
  Lemmas 2.1–2.2 and 3.1–3.4 become products (boxes);
* the variables `N_{i,j}` are `NvalSTS` / `NvalOF`, and the revealing lemmas `reveal_sts`,
  `reveal_of` show that they bound the number of values still possible for `X_{i,j}`;
* the two applications of Jensen's inequality of the paper (conditioning on the position of
  `i` in `≪` and on the position of `{i,j}` in the order of `E_i`) are `stepB_sts`/`stepA_sts`
  and `stepB_of`/`stepA_of`, combined in `expect_sts`/`expect_of`;
* the asymptotic evaluation of the resulting sums (the integrals
  `∫₀¹ 3x² log(n x³) …` of the paper) is in `RequestProject/LL/Estimates.lean`, with explicit
  error terms.
-/

@[expose] public section

namespace LinialLuria

/-- **Conjecture 1.3 (Steiner triple systems)** — open; stated only.
`STS(n) = ((1 + o(1)) n / e²)^{n²/6}` along the admissible orders `n ≡ 1, 3 (mod 6)`. -/
def Conjecture_1_3_STS : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, (n % 6 = 1 ∨ n % 6 = 3) →
    ((1 - ε) * n / Real.exp 2) ^ ((n : ℝ) ^ 2 / 6) ≤ (STS.D n : ℝ) ∧
    (STS.D n : ℝ) ≤ ((1 + ε) * n / Real.exp 2) ^ ((n : ℝ) ^ 2 / 6)

/-- **Conjecture 1.3 (1-factorizations)** — open; stated only.
`F(n) = ((1 + o(1)) n / e²)^{n²/2}` along the even orders `n`. -/
def Conjecture_1_3_F : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, n % 2 = 0 →
    ((1 - ε) * n / Real.exp 2) ^ ((n : ℝ) ^ 2 / 2) ≤ (F n : ℝ) ∧
    (F n : ℝ) ≤ ((1 + ε) * n / Real.exp 2) ^ ((n : ℝ) ^ 2 / 2)

/-- The upper halves of Conjecture 1.3 are Theorems 1.1 and 1.2. -/
theorem conjecture_1_3_upper_halves (ε : ℝ) (hε : 0 < ε) :
    (∀ᶠ n : ℕ in Filter.atTop,
      (STS.D n : ℝ) ≤ ((1 + ε) * n / Real.exp 2) ^ ((n : ℝ) ^ 2 / 6)) ∧
    (∀ᶠ n : ℕ in Filter.atTop,
      (F n : ℝ) ≤ ((1 + ε) * n / Real.exp 2) ^ ((n : ℝ) ^ 2 / 2)) :=
  ⟨theorem_1_1 ε hε, theorem_1_2 ε hε⟩

end LinialLuria
