/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LatinCount
public import RequestProject.NatBits

/-!
# Encoded states of partial Latin rectangles

States (column sets of a partial Latin rectangle of order `n ≤ 8`) are encoded as natural
numbers: bit `8 j + s` is set iff symbol `s` occurs in column `j`. These encodings are used by
the kernel-checkable certificate checker of `RequestProject.LatinKernel`.
-/

@[expose] public section

open Finset

namespace STS.LatinCompute

/-- Decoding a state. -/
def dec (n : ℕ) (x : ℕ) : Fin n → Finset (Fin n) :=
  fun j => univ.filter (fun s => x.testBit (8 * j + s))

lemma sum_zip_eq {α β : Type*} (l1 : List α) (l2 : List β) (f : α → ℕ) (g : β → ℕ)
    (hlen : l1.length = l2.length) (h : ∀ a b, (a, b) ∈ List.zip l1 l2 → f a = g b) :
    (l1.map f).sum = (l2.map g).sum := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons a l1 ih =>
    cases l2 with
    | nil => simp at hlen
    | cons b l2 =>
      simp only [List.map_cons, List.sum_cons]
      rw [h a b (by simp), ih l2 (by simpa using hlen) (fun a' b' hab => h a' b' (by simp [hab]))]

end STS.LatinCompute
