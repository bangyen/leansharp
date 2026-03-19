/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Examples.IllConditioned
import LeanSharp.Theory.Dynamics.Convergence
import LeanSharp.Theory.Dynamics.Schedulers

/-!
# Ill-Conditioned Landscape Tests

This module exists to validate that convergence theorems instantiate correctly
on harder example landscapes and schedule assumptions.

## Examples

* `advanced_schedule_convergence`.
-/

namespace LeanSharp.Tests

/-- **Advanced Verification**: Proves that the generalized convergence theorem
holds for the ill-conditioned landscape with a cosine decay schedule. -/
example (T : ℕ) (hT : T > 0) (η0 ρ z : ℝ)
    (h_bounds : 0 ≤ η0 ∧ η0 * 20 ^ 2 ≤ 2 ∧ η0 ≤ 1 / 20)
    (h_align : ∀ w : W (Fin 2), let ε := samPerturbation IllConditioned.L_advanced w ρ;
                AlignmentCondition IllConditioned.L_advanced w 0 ε z 2 20) :
    ZSharpConvergenceHolds IllConditioned.L_advanced 0
      (cosineDecaySchedule η0 0 T) ρ z 20 2 := by
  let M : ZSharpModel (Fin 2) := {
    L := IllConditioned.L_advanced_bundled,
    w_star := 0,
    ρ := ρ,
    z := z,
    alignment := h_align
  }
  apply zsharp_convergence M
  · intro t; rw [cosineDecaySchedule]
    have h_mono : cosineDecaySchedule η0 0 T t ≤ cosineDecaySchedule η0 0 T 0 :=
      cosine_decay_antitone η0 0 T (by linarith) (Nat.zero_le t)
    have h_eta0 : η0 = cosineDecaySchedule η0 0 T 0 := by
      rw [cosine_decay_zero η0 0 T hT]
    rw [← h_eta0] at h_mono
    calc cosineDecaySchedule η0 0 T t * (M.L.smoothness : ℝ) ^ 2
      _ ≤ η0 * 20 ^ 2 := mul_le_mul_of_nonneg_right h_mono (by norm_num)
      _ ≤ 2 := h_bounds.2.1
      _ = M.L.μ := rfl
  · change (2 : ℝ) < 20; norm_num

end LeanSharp.Tests
