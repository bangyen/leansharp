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
    (h_align : ∀ w : W (Fin 2),
                let g_f := gradient IllConditioned.advancedLoss
                  (w + zsharpPerturbation IllConditioned.advancedLoss w
                    (fun _ => ()) ρ z)
                AlignmentCondition w 0 g_f 2 20) :
    ZSharpConvergenceHolds IllConditioned.advancedLoss 0
      (cosineDecaySchedule η0 0 T) (fun _ => ()) ρ z 20 2 := by
  -- A 2-D toy landscape is a single layer, so the partition is constant.
  let M : ZSharpModel (Fin 2) Unit := {
    L := IllConditioned.advancedLossBundled,
    w_star := 0,
    ρ := ρ,
    z := z,
    π := fun _ => (),
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
