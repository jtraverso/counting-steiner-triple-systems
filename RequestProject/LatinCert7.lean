/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LatinJobs7_0

/-! The certificate for `L(7)`: all its parts, and the global consistency check. -/

@[expose] public section

set_option maxRecDepth 100000

namespace STS.LatinKernel

/-- All the jobs for `L(7)`. -/
def jobs7 : List Job :=
  jobs7_0

theorem jobs7_ok : jobsOk 7 tree7 jobs7 = true := by
  simp only [jobs7, jobsOk_append, jobs7_0_ok, Bool.and_self]

set_option maxHeartbeats 0 in
theorem cert7_ok : certOk 7 reps7 tree7 jobs7 = true := by
  decide +kernel

theorem root7 :
    (reps7.map (fun R => (R.x, R.r, R.v))).head? = some (0, 7, 61479419904000) := by
  decide +kernel

end STS.LatinKernel
