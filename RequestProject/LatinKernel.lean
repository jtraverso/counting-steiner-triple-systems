/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LatinCount

/-!
# A kernel-checkable certificate checker for `L(n)`, `n ≤ 8`
-/

@[expose] public section

namespace STS.LatinKernel

/-- Bit `i` of `m`. -/
def bit (m i : ℕ) : Bool := Nat.beq ((m >>> i) % 2) 1

/-- The set of symbols of a list, as a bit mask. -/
def bitsOf : List ℕ → ℕ
  | [] => 0
  | s :: l => 2 ^ s ||| bitsOf l

/-- The admissible ways to fill the columns `j, j+1, …, j+k-1` of a new row, given the state
`x` and the set `u` of symbols already used in the row. -/
def gen (n x : ℕ) : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => [[]]
  | k + 1, j, u => (List.range n).flatMap fun s =>
      bif bit u s || bit x (8 * j + s) then [] else (gen n x k (j + 1) (u ||| 2 ^ s)).map (s :: ·)

/-- The mask of a (partial) row starting at column `j`. -/
def maskL : ℕ → List ℕ → ℕ
  | _, [] => 0
  | j, s :: l => 2 ^ (8 * j + s) ||| maskL (j + 1) l

/-- The bit mask selecting bit `0` of each column. -/
def lowBits : ℕ := 0x0101010101010101

/-- The image of the symbol `s` under the relabelling encoded by `c`. -/
def tauOf (c s : ℕ) : ℕ := (c >>> (3 * s)) % 8

/-- Relabelling the symbols of a state. -/
def relab (n y c : ℕ) : ℕ :=
  (List.range n).foldl (fun acc s => acc ||| (((y >>> s) &&& lowBits) <<< tauOf c s)) 0

/-- The relabelling code `c` describes a permutation of `{0, …, n-1}`. -/
def permOk (n c : ℕ) : Bool :=
  Nat.beq ((List.range n).foldl (fun acc s => acc ||| 2 ^ tauOf c s) 0) (2 ^ n - 1)

/-- The columns of a state. -/
def cols (n z : ℕ) : List ℕ := (List.range n).map fun j => (z >>> (8 * j)) % 256

/-- Reassembling a state from its columns. -/
def ofCols : List ℕ → ℕ
  | [] => 0
  | c :: l => c + 256 * ofCols l

/-- Insertion into a sorted list. -/
def ins (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => bif Nat.ble a b then a :: b :: l else b :: ins a l

/-- Insertion sort. -/
def isort : List ℕ → List ℕ
  | [] => []
  | a :: l => ins a (isort l)

/-- The canonical form of the state `y` relabelled by `c`: relabel, then sort the columns. -/
def canon (n y c : ℕ) : ℕ := ofCols (isort (cols n (relab n y c)))

/-- Lookup trees. -/
inductive KT where
  | leaf : KT
  | node : KT → ℕ → ℕ → ℕ → KT → KT

/-- Looking up a key. -/
def KT.find : KT → ℕ → Option (ℕ × ℕ)
  | .leaf, _ => none
  | .node l k r v t, z =>
    bif Nat.beq z k then some (r, v) else bif Nat.blt z k then l.find z else t.find z

/-- Decoding `k` codes of 24 bits. -/
def decW : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, w => w % 2 ^ 24 :: decW k (w >>> 24)

/-- Decoding the code words of a job. -/
def codesOf (ws : List ℕ) : List ℕ := ws.flatMap (decW 15)

/-- The value of a child. -/
def childVal (n x r : ℕ) (T : KT) (l : List ℕ) (c : ℕ) : Option ℕ :=
  bif permOk n c then
    match T.find (canon n (x ||| maskL 0 l) c) with
    | some (r', v') => bif Nat.beq r' r then some v' else none
    | none => none
  else none

/-- Summing the values of the children `p ++ l`, `l ∈ ls`. -/
def sumKids (n x r : ℕ) (T : KT) (p : List ℕ) : List (List ℕ) → List ℕ → ℕ → Option ℕ
  | [], _, acc => some acc
  | _ :: _, [], _ => none
  | l :: ls, c :: cs, acc =>
    match childVal n x r T (p ++ l) c with
    | some v => sumKids n x r T p ls cs (acc + v)
    | none => none

/-- A representative: state, rows left, value, first symbol of the next row, prefix length,
subtotals. -/
structure Rep where
  x : ℕ
  r : ℕ
  v : ℕ
  a : ℕ
  d : ℕ
  ws : List ℕ

/-- A job: state, rows left, prefix, subtotal, code words. -/
structure Job where
  x : ℕ
  r : ℕ
  p : List ℕ
  w : ℕ
  codes : List ℕ

/-- Checking a job. -/
def jobCheck (n : ℕ) (T : KT) (J : Job) : Bool :=
  match J.r with
  | 0 => false
  | r + 1 =>
    match sumKids n J.x r T J.p (gen n J.x (n - J.p.length) J.p.length (bitsOf J.p))
      (codesOf J.codes) 0 with
    | some s => Nat.beq s J.w
    | none => false

/-- Checking a list of jobs. -/
def jobsOk (n : ℕ) (T : KT) (js : List Job) : Bool := js.all (jobCheck n T)

lemma jobsOk_append (n : ℕ) (T : KT) (a b : List Job) :
    jobsOk n T (a ++ b) = (jobsOk n T a && jobsOk n T b) := by
  simp [jobsOk, List.all_append]

/-- The number of bits among the first `s` bits of `x`. -/
def popc (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => popc x s + (x >>> s) % 2

/-- The headers of the jobs belonging to a representative. -/
def repHeaders (n : ℕ) (R : Rep) : List (ℕ × ℕ × List ℕ × ℕ) :=
  ((gen n R.x (R.d - 1) 1 (2 ^ R.a)).zip R.ws).map fun q => (R.x, R.r, R.a :: q.1, q.2)

/-- Checking a representative. -/
def repCheck (n : ℕ) (R : Rep) : Bool :=
  match R.r with
  | 0 => Nat.beq R.v 1
  | r + 1 => !bit R.x R.a && Nat.blt R.a n && Nat.beq (popc R.x n + (r + 1)) n &&
      Nat.ble 1 R.d && Nat.ble R.d n &&
      Nat.beq (gen n R.x (R.d - 1) 1 (2 ^ R.a)).length R.ws.length &&
      Nat.beq R.v ((r + 1) * R.ws.sum)

/-- The in-order list of the entries of a lookup tree. -/
def KT.toList : KT → List (ℕ × ℕ × ℕ)
  | .leaf => []
  | .node l k r v t => l.toList ++ (k, r, v) :: t.toList

/-- The header of a job. -/
def Job.header (J : Job) : ℕ × ℕ × List ℕ × ℕ := (J.x, J.r, J.p, J.w)

/-- The global consistency check of a certificate. -/
def certOk (n : ℕ) (reps : List Rep) (T : KT) (jobs : List Job) : Bool :=
  reps.all (repCheck n) && T.toList == reps.map (fun R => (R.x, R.r, R.v)) &&
    jobs.map Job.header == reps.flatMap (repHeaders n)

end STS.LatinKernel
