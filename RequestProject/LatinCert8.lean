/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.LatinJobs8_0
public import RequestProject.LatinJobs8_1
public import RequestProject.LatinJobs8_2
public import RequestProject.LatinJobs8_3
public import RequestProject.LatinJobs8_4
public import RequestProject.LatinJobs8_5

/-! The certificate for `L(8)`: all its parts, and the global consistency check. -/

@[expose] public section

set_option maxRecDepth 100000

namespace STS.LatinKernel

/-- All the jobs for `L(8)`. -/
def jobs8 : List Job :=
  jobs8_0 ++ jobs8_1 ++ jobs8_2 ++ jobs8_3 ++ jobs8_4 ++ jobs8_5

theorem jobs8_ok : jobsOk 8 tree8 jobs8 = true := by
  simp only [jobs8, jobsOk_append, jobs8_0_ok, jobs8_1_ok, jobs8_2_ok, jobs8_3_ok, jobs8_4_ok,
    jobs8_5_ok, Bool.and_self]

set_option maxHeartbeats 0 in
theorem cert8_ok : certOk 8 reps8 tree8 jobs8 = true := by
  decide +kernel

theorem root8 :
    (reps8.map (fun R => (R.x, R.r, R.v))).head? = some (0, 8, 108776032459082956800) := by
  decide +kernel

end STS.LatinKernel
