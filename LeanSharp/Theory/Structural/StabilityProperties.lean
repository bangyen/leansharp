/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Layers.Basic.Residual
import LeanSharp.Theory.Structural.ChainStability

namespace LeanSharp

/-!
# Training Stability Proofs

This module proves that Z-score filtering maintains the stability of
neural network architectures, particularly Residual blocks.

## Theorems

* `filtered_update_stability`.
* `localized_filtered_update_norm_bound`.
* `localized_filtered_update_norm_bound_of_reference`.
* `uniform_filtered_process_stability`.
* `residual_filtered_stability`.
-/

variable {ι : Type*} [Fintype ι]

/-- **Z-score Update Stability**:
    The norm of the update with a filtered gradient is always less than or equal
    to the norm of the update with the original gradient. -/
theorem filtered_update_stability (w g : W ι) (η z : ℝ) :
    ‖(w - η • filteredGradient g z) - w‖ ≤ ‖(w - η • g) - w‖ := by
  simp only [sub_sub_cancel_left, norm_neg, norm_smul]
  apply mul_le_mul_of_nonneg_left (norm_filteredGradient_le g z)
  positivity

/-- **Localized One-Step Stability Bound**: if the gradient norm at a step is
bounded by `R`, then the Z-filtered parameter update has norm at most `|η| * R`.
This gives a localized per-step drift certificate for deterministic stability
arguments. -/
theorem localized_filtered_update_norm_bound
    (w g : W ι) (η z R : ℝ)
    (hR : ‖g‖ ≤ R) :
    ‖(w - η • filteredGradient g z) - w‖ ≤ |η| * R := by
  have h_step := filtered_update_stability w g η z
  calc
    ‖(w - η • filteredGradient g z) - w‖
      ≤ ‖(w - η • g) - w‖ := h_step
    _ = |η| * ‖g‖ := by
      simp only [sub_sub_cancel_left, norm_neg, norm_smul]
      rw [Real.norm_eq_abs]
    _ ≤ |η| * R := mul_le_mul_of_nonneg_left hR (abs_nonneg η)

/-- **Reference-Based Localized Stability Bound**: if `g_ref` is a trusted local
reference gradient and `g` stays within radius `Δ` of it, then the filtered
update magnitude is bounded by `|η| * (R_ref + Δ)`, where `R_ref` bounds the
reference gradient norm. -/
theorem localized_filtered_update_norm_bound_of_reference
    (w g g_ref : W ι) (η z R_ref Δ : ℝ)
    (h_ref : ‖g_ref‖ ≤ R_ref)
    (h_loc : ‖g - g_ref‖ ≤ Δ) :
    ‖(w - η • filteredGradient g z) - w‖ ≤ |η| * (R_ref + Δ) := by
  have h_norm_g : ‖g‖ ≤ R_ref + Δ := by
    calc
      ‖g‖ = ‖(g - g_ref) + g_ref‖ := by abel_nf
      _ ≤ ‖g - g_ref‖ + ‖g_ref‖ := norm_add_le _ _
      _ ≤ Δ + R_ref := add_le_add h_loc h_ref
      _ = R_ref + Δ := by ring
  exact localized_filtered_update_norm_bound w g η z (R_ref + Δ) h_norm_g

/-- **Uniform Process Stability**: if each filtered update follows the standard
step rule and each step gradient norm is bounded by `R`, then the distance from
the initial point after `T` steps is bounded by the accumulated per-step drift
budget. This is the sequence-level deterministic stability theorem for the
entire filtered process. -/
theorem uniform_filtered_process_stability
    (w : ℕ → W ι) (g : ℕ → W ι) (η : ℕ → ℝ) (z R : ℝ)
    (h_step : ∀ t, w (t + 1) = w t - η t • filteredGradient (g t) z)
    (hR : ∀ t, ‖g t‖ ≤ R) :
    ∀ T : ℕ, ‖w T - w 0‖ ≤ Finset.sum (Finset.range T) (fun t => |η t| * R) := by
  intro T
  induction T with
  | zero =>
      simp only [
        sub_self,
        norm_zero,
        Finset.range_zero,
        Finset.sum_empty,
        le_refl
      ]
  | succ t ih =>
      have h_inc : ‖w (t + 1) - w t‖ ≤ |η t| * R := by
        rw [h_step t]
        exact localized_filtered_update_norm_bound (w t) (g t) (η t) z R (hR t)
      have h_triangle : ‖w (t + 1) - w 0‖ ≤ ‖w (t + 1) - w t‖ + ‖w t - w 0‖ := by
        have hsplit : w (t + 1) - w 0 = (w (t + 1) - w t) + (w t - w 0) := by abel
        rw [hsplit]
        exact norm_add_le _ _
      calc
        ‖w (t + 1) - w 0‖
            ≤ ‖w (t + 1) - w t‖ + ‖w t - w 0‖ := h_triangle
        _ ≤ |η t| * R + Finset.sum (Finset.range t) (fun x => |η x| * R) := add_le_add h_inc ih
        _ = Finset.sum (Finset.range (t + 1)) (fun x => |η x| * R) := by
              rw [Finset.sum_range_succ]
              ring

/-- **Residual Continuity Stability**:
    In a residual block $y = x + f(x)$, if the filtered update to the parameters
    of $f$ is bounded, then the change in the output is also bounded.
    (This is a structural lemma for deterministic stability). -/
theorem residual_filtered_stability {ι_in : Type} [Fintype ι_in]
    (f : Layer (W ι_in) (W ι_in)) (w g : W f.ParamDim) (x : W ι_in) (η z : ℝ)
    (h_lip : LipschitzWith K (fun w' => f.forward w' x)) :
    ‖(residualLayer f).forward (w - η • filteredGradient g z) x -
      (residualLayer f).forward w x‖ ≤ K * |η| * ‖g‖ := by
  unfold residualLayer
  rw [add_sub_add_left_eq_sub]
  -- Use Lipschitz property
  have h_bound := h_lip.norm_sub_le (w - η • filteredGradient g z) w
  apply h_bound.trans
  rw [sub_sub_cancel_left, norm_neg, norm_smul]
  rw [Real.norm_eq_abs, ← mul_assoc]
  apply mul_le_mul_of_nonneg_left
  · exact norm_filteredGradient_le g z
  · positivity

end LeanSharp
