/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Theory.Dynamics.Convergence
import LeanSharp.Theory.Dynamics.Schedulers

/-!
# Schedule Convergence Tests

This module exists to verify that scheduler-specific assumptions integrate with
the generic convergence theorem in representative toy settings.

## Theorems

* `toy_cosine_convergence`.
-/

namespace LeanSharp

/-- **Schedule Convergence Verification**: A toy example demonstrating that
the generalized convergence theorem can be applied to `cosine_decay_schedule`. -/
theorem toy_cosine_convergence (T : ℕ) (hT : T > 0)
    (L : StronglyConvexObjective (Fin 2)) (η0 ρ z : ℝ)
    (h_bounds : 0 ≤ η0 ∧ η0 * (L.smoothness : ℝ) ^ 2 ≤ L.μ ∧
      η0 ≤ 1 / (L.smoothness : ℝ) ∧ L.μ < (L.smoothness : ℝ))
    (h_align : ∀ w : W (Fin 2), let ε := sam_perturbation L.toFun w ρ;
                alignment_condition L.toFun w 0 ε z L.μ L.smoothness) :
    zsharp_convergence_holds L.toFun 0
      (cosine_decay_schedule η0 0 T) ρ z L.smoothness L.μ := by
  apply zsharp_convergence L
  · intro t; rw [cosine_decay_schedule]
    -- Proof that η_t * L_smooth^2 ≤ μ
    -- η_t ≤ η0 since cosine decay is antitone
    have h_mono : cosine_decay_schedule η0 0 T t ≤ cosine_decay_schedule η0 0 T 0 :=
      cosine_decay_antitone η0 0 T (by linarith) (Nat.zero_le t)
    have h_eta0 : η0 = cosine_decay_schedule η0 0 T 0 := by
      rw [cosine_decay_zero η0 0 T hT]
    rw [← h_eta0] at h_mono
    calc cosine_decay_schedule η0 0 T t * (L.smoothness : ℝ) ^ 2
      _ ≤ η0 * (L.smoothness : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h_mono (sq_nonneg _)
      _ ≤ L.μ := h_bounds.2.1
  · exact h_bounds.2.2.2
  · exact h_align

end LeanSharp
