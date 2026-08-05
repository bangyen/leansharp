/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Theory.Alignment
import LeanSharp.Theory.Dynamics.Convergence

/-!
# Quadratic Bowl Tests

This module exists to sanity-check foundational properties of toy model
gradients and filtering behavior used throughout proof examples.

## Examples

* `test_toy_filter_contraction`.
* `test_toy_filter_identity`.
* `test_toy_gradient_nonzero`.
-/

namespace LeanSharp.Tests

open LeanSharp.QuadraticBowl
open MeasureTheory

/-- Verifies the fundamental L2 contraction property of the Z-score filter on the toy model. -/
example :
    ‖filteredGradient (exactGradientToy wInit) 1‖ ≤ ‖exactGradientToy wInit‖ := by
  apply norm_filtered_gradient_le

/-- Verifies that for the toy gradient, the Z-score filter (z=1) is an identity. -/
example :
    filteredGradient (exactGradientToy wInit) 1 = (exactGradientToy wInit) := by
  have h_mean : vectorMean (exactGradientToy wInit) = 4 := by
    unfold vectorMean exactGradientToy wInit
    rw [Equiv.apply_symm_apply]
    norm_num
  have h_std : vectorStd (exactGradientToy wInit) = 2 := by
    have h_var : vectorVariance (exactGradientToy wInit) = 4 := by
      unfold vectorVariance
      rw [h_mean]
      unfold exactGradientToy wInit
      rw [Equiv.apply_symm_apply]
      norm_num
    unfold vectorStd
    rw [h_var]
    have h_sq : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [← h_sq, Real.sqrt_sq (by norm_num)]
  unfold filteredGradient zScoreMask hadamard
  rw [h_mean, h_std]
  ext i
  dsimp only [
    Equiv.symm_apply_apply,
    Equiv.apply_symm_apply,
    WithLp.equiv_symm_apply,
    WithLp.equiv_apply
  ]
  fin_cases i <;> {
    unfold exactGradientToy wInit
    split_ifs with h <;> norm_num at *
  }

/-- Verifies that the toy model's gradient at the initial point is non-zero. -/
example :
    exactGradientToy wInit ≠ 0 := by
  unfold exactGradientToy wInit
  intro h
  have h0 : (WithLp.equiv 2 (Fin 2 → ℝ) ((WithLp.equiv 2 (Fin 2 → ℝ)).symm fun i =>
      2 * (WithLp.equiv 2 (Fin 2 → ℝ)) ((WithLp.equiv 2 (Fin 2 → ℝ)).symm fun i =>
        if i = 0 then 1 else 3) i)) 0 = 0 := by
    rw [h]; rfl
  rw [Equiv.apply_symm_apply] at h0
  norm_num at h0

/-- Verifies that the computed gradient equals the analytical gradient of the toy loss. -/
example (w : W (Fin 2)) :
    gradient toyLoss w = exactGradientToy w := by
  exact gradient_toy_eq w

/-- Verifies that the toy gradient is 2-Lipschitz. -/
example (w v : W (Fin 2)) :
    ‖gradient toyLoss w - gradient toyLoss v‖ ≤ 2 * ‖w - v‖ :=
  toy_L_smooth.2 w v

/-- Verifies that the toy loss is 2-strongly convex. -/
example (w v : W (Fin 2)) :
    toyLoss v ≥ toyLoss w + inner ℝ (gradient toyLoss w) (v - w) +
      (2 / 2) * ‖v - w‖ ^ 2 :=
  toy_strongly_convex.2 w v

/-- Verifies the bundled objective exposes the expected constants. -/
example :
    QuadraticBowl.toyLossBundled.μ = 2 ∧ QuadraticBowl.toyLossBundled.smoothness = 2 := by
  constructor <;> rfl

/-- The alignment bridge derives the convergence alignment hypothesis for the
SAM-perturbed quadratic-bowl gradient from pointwise signal-noise conditions. -/
example {Ω : Type*} [MeasureSpace Ω] (ω : Ω) (w w_star : W (Fin 2))
    (ρ z μ L_smooth : ℝ)
    (h_align : μ * ‖w - w_star‖ ^ 2 ≤
      inner ℝ (gradient toyLoss (w + samPerturbation toyLoss w ρ)) (w - w_star))
    (h_norm : ‖filteredGradient (gradient toyLoss (w + samPerturbation toyLoss w ρ)) z‖ ≤
      L_smooth * ‖w - w_star‖)
    (h_safe : ∀ i : Fin 2,
      (WithLp.equiv 2 (Fin 2 → ℝ)
        (zScoreMask (gradient toyLoss (w + samPerturbation toyLoss w ρ)) z)) i = 0 →
      (WithLp.equiv 2 (Fin 2 → ℝ) (w - w_star) i) *
        (WithLp.equiv 2 (Fin 2 → ℝ)
          (gradient toyLoss (w + samPerturbation toyLoss w ρ)) i) ≤ 0) :
    AlignmentCondition w w_star
      (filteredGradient (gradient toyLoss (w + samPerturbation toyLoss w ρ)) z) μ L_smooth := by
  exact alignment_of_sam_signal_conditions Ω ω toyLoss w w_star ρ z μ L_smooth
    h_align h_norm h_safe

end LeanSharp.Tests
