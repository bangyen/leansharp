/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Layers.Residual
import LeanSharp.Theory.ChainStability

namespace LeanSharp

/-!
# Training Stability Proofs

This module proves that Z-score filtering maintains the stability of
neural network architectures, particularly Residual blocks.
-/

variable {ι : Type*} [Fintype ι]

/-- **Z-score Update Stability**:
    The norm of the update with a filtered gradient is always less than or equal
    to the norm of the update with the original gradient. -/
theorem filtered_update_stability (w g : W ι) (η z : ℝ) (hη : 0 ≤ η) :
    ‖(w - η • filtered_gradient g z) - w‖ ≤ ‖(w - η • g) - w‖ := by
  simp only [sub_sub_cancel_left, norm_neg, norm_smul]
  have h_norm : ‖η‖ = η := by rw [Real.norm_eq_abs, abs_of_nonneg hη]
  rw [h_norm]
  apply mul_le_mul_of_nonneg_left (filtered_norm_bound g z) hη

/-- **Residual Continuity Stability**:
    In a residual block $y = x + f(x)$, if the filtered update to the parameters
    of $f$ is bounded, then the change in the output is also bounded.
    (This is a structural lemma for deterministic stability). -/
theorem residual_filtered_stability {ι_in : Type} [Fintype ι_in]
    (f : Layer (W ι_in) (W ι_in)) (w g : W f.ParamDim) (x : W ι_in) (η z : ℝ)
    (hη : 0 ≤ η) (h_lip : LipschitzWith K (fun w' => f.forward w' x)) :
    ‖(residual_layer f).forward (w - η • filtered_gradient g z) x -
      (residual_layer f).forward w x‖ ≤ K * η * ‖g‖ := by
  unfold residual_layer
  simp only [add_sub_add_left_eq_sub]
  -- Use Lipschitz property
  have h_bound := h_lip.norm_sub_le (w - η • filtered_gradient g z) w
  apply h_bound.trans
  simp only [sub_sub_cancel_left, norm_neg, norm_smul]
  have h_norm : ‖η‖ = η := by rw [Real.norm_eq_abs, abs_of_nonneg hη]
  rw [h_norm, ← mul_assoc]
  apply mul_le_mul_of_nonneg_left
  · exact filtered_norm_bound g z
  · positivity

end LeanSharp
