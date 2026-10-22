/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LatinJobs6_0

/-! The certificate for `L(6)`: all its parts, and the global consistency check. -/

@[expose] public section

set_option maxRecDepth 100000

namespace STS.LatinKernel

/-- All the jobs for `L(6)`. -/
def jobs6 : List Job :=
  jobs6_0

theorem jobs6_ok : jobsOk 6 tree6 jobs6 = true := by
  simp only [jobs6, jobsOk_append, jobs6_0_ok, Bool.and_self]

set_option maxHeartbeats 0 in
theorem cert6_ok : certOk 6 reps6 tree6 jobs6 = true := by
  decide +kernel

theorem root6 :
    (reps6.map (fun R => (R.x, R.r, R.v))).head? = some (0, 6, 812851200) := by
  decide +kernel

end STS.LatinKernel
