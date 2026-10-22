/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.ExplicitData
public import RequestProject.STSKernel

/-!
# Verification of the explicit Steiner triple systems

The properties of the explicit systems listed in `RequestProject.ExplicitData` are checked by
the kernel, using the verified checker `STS.stsOK` (`STS.isSTS_of_stsOK`) and the inclusion
criterion `STS.fanoIn_subset_of`.
-/

@[expose] public section

namespace STS

lemma isSTS_fano : IsSTS fano := by
  rw [fano_eq]; exact isSTS_of_stsOK (by decide +kernel)

lemma isSTS_fanoIn7 : IsSTS (fanoIn 7) := by
  have h : (Fin.castLE (le_refl 7) : Fin 7 → Fin 7) = id := funext fun x => Fin.ext rfl
  rw [fanoIn, dite_eq_left (le_refl 7), h, mapBlocks_id]
  exact isSTS_fano

lemma isSTS_empty1 : IsSTS (∅ : Finset (Finset (Fin 1))) :=
  ⟨by simp, fun x y hxy => absurd (Subsingleton.elim x y) hxy⟩

lemma isSTS_ofTriples3 : IsSTS (ofTriples 3 [(0, 1, 2)]) := isSTS_of_stsOK (by decide +kernel)
lemma isSTS_ofTriples9 : IsSTS (ofTriples 9 triples9) := isSTS_of_stsOK (by decide +kernel)
lemma isSTS_ofTriples13 : IsSTS (ofTriples 13 triples13) := isSTS_of_stsOK (by decide +kernel)
lemma isSTS_ofTriples25 : IsSTS (ofTriples 25 triples25) := isSTS_of_stsOK (by decide +kernel)
lemma isSTS_ofTriples27 : IsSTS (ofTriples 27 triples27) := isSTS_of_stsOK (by decide +kernel)
lemma isSTS_ofTriples33 : IsSTS (ofTriples 33 triples33) := isSTS_of_stsOK (by decide +kernel)
lemma isSTS_ofTriples37 : IsSTS (ofTriples 37 triples37) := isSTS_of_stsOK (by decide +kernel)
lemma isSTS_ofTriples39 : IsSTS (ofTriples 39 triples39) := isSTS_of_stsOK (by decide +kernel)

lemma fanoIn_subset25 : fanoIn 25 ⊆ ofTriples 25 triples25 :=
  fanoIn_subset_of (by norm_num) (by decide +kernel)
lemma fanoIn_subset27 : fanoIn 27 ⊆ ofTriples 27 triples27 :=
  fanoIn_subset_of (by norm_num) (by decide +kernel)
lemma fanoIn_subset33 : fanoIn 33 ⊆ ofTriples 33 triples33 :=
  fanoIn_subset_of (by norm_num) (by decide +kernel)
lemma fanoIn_subset37 : fanoIn 37 ⊆ ofTriples 37 triples37 :=
  fanoIn_subset_of (by norm_num) (by decide +kernel)
lemma fanoIn_subset39 : fanoIn 39 ⊆ ofTriples 39 triples39 :=
  fanoIn_subset_of (by norm_num) (by decide +kernel)

end STS
