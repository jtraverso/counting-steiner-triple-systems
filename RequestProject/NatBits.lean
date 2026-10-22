/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Bits of natural numbers built by folding
-/

@[expose] public section

namespace STS

lemma testBit_foldl {α : Type*} (f : ℕ → α → ℕ) (P : α → ℕ → Bool)
    (hf : ∀ acc a i, (f acc a).testBit i = (acc.testBit i || P a i)) (l : List α) (init i : ℕ) :
    (l.foldl f init).testBit i = (init.testBit i || l.any (fun a => P a i)) := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [List.foldl, ih, hf, Bool.or_assoc]

end STS
