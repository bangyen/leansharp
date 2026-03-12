/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Schedulers
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace LeanSharp.Tests

/-- Unit test: Verify starting learning rate is η_max. -/
theorem test_cosine_decay_start :
    cosine_decay_schedule 0.1 0.01 100 0 = 0.1 := by
  apply cosine_decay_zero
  norm_num

/-- Unit test: Verify ending learning rate is η_min. -/
theorem test_cosine_decay_end :
    cosine_decay_schedule 0.1 0.01 100 100 = 0.01 := by
  apply cosine_decay_at_T

/-- Unit test: Verify monotonicity for a specific range. -/
theorem test_cosine_decay_mono :
    cosine_decay_schedule 0.1 0.01 100 50 ≤ cosine_decay_schedule 0.1 0.01 100 25 := by
  apply cosine_decay_antitone
  · norm_num
  · norm_num

end LeanSharp.Tests
