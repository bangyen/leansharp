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
the generalized convergence theorem can be applied to `cosineDecaySchedule`. -/
theorem toy_cosine_convergence (T : ℕ) (hT : T > 0)
    (L : StronglyConvexObjective (Fin 2)) (η0 ρ z : ℝ)
    (h_bounds : 0 ≤ η0 ∧ η0 * (L.smoothness : ℝ) ^ 2 ≤ L.μ ∧
      η0 ≤ 1 / (L.smoothness : ℝ) ∧ L.μ < (L.smoothness : ℝ))
    (h_align : ∀ w : W (Fin 2), let ε := samPerturbation L.toFun w ρ;
                AlignmentCondition L.toFun w 0 ε z L.μ L.smoothness) :
    ZSharpConvergenceHolds L.toFun 0
      (cosineDecaySchedule η0 0 T) ρ z L.smoothness L.μ := by
  let M : ZSharpModel (Fin 2) := {
    L := L,
    w_star := 0,
    ρ := ρ,
    z := z,
    alignment := h_align
  }
  apply zsharp_convergence M
  · intro t; rw [cosineDecaySchedule]
    -- Proof that η_t * L_smooth^2 ≤ μ
    -- η_t ≤ η0 since cosine decay is antitone
    have h_mono : cosineDecaySchedule η0 0 T t ≤ cosineDecaySchedule η0 0 T 0 :=
      cosine_decay_antitone η0 0 T (by linarith) (Nat.zero_le t)
    have h_eta0 : η0 = cosineDecaySchedule η0 0 T 0 := by
      rw [cosine_decay_zero η0 0 T hT]
    rw [← h_eta0] at h_mono
    calc cosineDecaySchedule η0 0 T t * (M.L.smoothness : ℝ) ^ 2
      _ ≤ η0 * (M.L.smoothness : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h_mono (sq_nonneg _)
      _ ≤ M.L.μ := h_bounds.2.1
  · exact h_bounds.2.2.2

end LeanSharp
