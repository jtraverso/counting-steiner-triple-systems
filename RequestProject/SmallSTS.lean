/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.SmallSTSData

/-!
# There are (at least) 30 STS's on a 7-set and 840 STS's on a 9-set

The images of the Fano plane (resp. of the affine plane of order 3) under the permutations
listed in `RequestProject.SmallSTSData` are pairwise distinct; this is checked by the kernel
with the verified checker `STS.countCheck` (`STS.length_le_D_of_countCheck`).
-/

@[expose] public section

namespace STS

lemma countCheck7 : countCheck 7 fanoT perms7 = true := by decide +kernel

lemma countCheck9 : countCheck 9 ag9T perms9 = true := by decide +kernel

/-- There are at least 30 STS's on a fixed 7-set (in fact exactly 30). -/
theorem D7_ge : 30 ≤ D 7 := by
  have h := length_le_D_of_countCheck countCheck7
  have hl : perms7.length = 30 := by decide +kernel
  omega

/-- There are at least 840 STS's on a fixed 9-set (in fact exactly 840). -/
theorem D9_ge : 840 ≤ D 9 := by
  have h := length_le_D_of_countCheck countCheck9
  have hl : perms9.length = 840 := by decide +kernel
  omega

end STS
