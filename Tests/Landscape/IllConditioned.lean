/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Examples.IllConditioned
import LeanSharp.Theory.Dynamics.Convergence
import LeanSharp.Theory.Dynamics.Schedulers

/-!
# Advanced Verification Tests

This module exists to validate that convergence theorems instantiate correctly
on harder example landscapes and schedule assumptions.

## Theorems

* `advanced_schedule_convergence`.
-/

namespace LeanSharp

/-- **Advanced Verification**: Proves that the generalized convergence theorem
holds for the ill-conditioned landscape with a cosine decay schedule. -/
theorem advanced_schedule_convergence (T : ℕ) (hT : T > 0) (η0 ρ z : ℝ)
    (h_bounds : 0 ≤ η0 ∧ η0 * 20 ^ 2 ≤ 2 ∧ η0 ≤ 1 / 20)
    (h_align : ∀ w : W (Fin 2), let ε := sam_perturbation IllConditioned.L_advanced w ρ;
                alignment_condition IllConditioned.L_advanced w 0 ε z 2 20) :
    zsharp_convergence_holds IllConditioned.L_advanced 0
      (cosine_decay_schedule η0 0 T) ρ z 20 2 := by
  let L := IllConditioned.L_advanced_bundled
  apply zsharp_convergence L
  · intro t; rw [cosine_decay_schedule]
    have h_mono : cosine_decay_schedule η0 0 T t ≤ cosine_decay_schedule η0 0 T 0 :=
      cosine_decay_antitone η0 0 T (by linarith) (Nat.zero_le t)
    have h_eta0 : η0 = cosine_decay_schedule η0 0 T 0 := by
      rw [cosine_decay_zero η0 0 T hT]
    rw [← h_eta0] at h_mono
    calc cosine_decay_schedule η0 0 T t * (L.smoothness : ℝ) ^ 2
      _ ≤ η0 * 20 ^ 2 := mul_le_mul_of_nonneg_right h_mono (by norm_num)
      _ ≤ 2 := h_bounds.2.1
      _ = L.μ := rfl
  · change (2 : ℝ) < 20; norm_num
  · exact h_align

end LeanSharp
