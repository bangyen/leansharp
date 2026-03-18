/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# Hard-Thresholding Structural Properties

This module formalizes core properties of hard-thresholding, including the
non-Lipschitz behavior used in deterministic stability analysis.

## Definitions

* `hard_threshold_scalar`.
* `hard_threshold`.

## Theorems

* `hard_threshold_scalar_abs_le`.
* `hard_threshold_scalar_idempotent`.
* `hard_threshold_idempotent`.
* `hard_threshold_scalar_not_lipschitz`.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι]

/-- Scalar hard-thresholding at radius `τ`. -/
noncomputable def hard_threshold_scalar (x τ : ℝ) : ℝ :=
  if |x| < τ then 0 else x

/-- Coordinate-wise hard-thresholding on vectors. -/
noncomputable def hard_threshold (w : W ι) (τ : ℝ) : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm
    (fun i => hard_threshold_scalar ((WithLp.equiv 2 (ι → ℝ) w) i) τ)

/-- Hard-thresholding never increases absolute value. -/
theorem hard_threshold_scalar_abs_le (x τ : ℝ) :
    |hard_threshold_scalar x τ| ≤ |x| := by
  by_cases h : |x| < τ
  · simp only [hard_threshold_scalar, h, ↓reduceIte, abs_zero, abs_nonneg]
  · simp only [hard_threshold_scalar, h, ↓reduceIte, le_refl]

/-- Hard-thresholding is idempotent in the scalar case. -/
theorem hard_threshold_scalar_idempotent (x τ : ℝ) :
    hard_threshold_scalar (hard_threshold_scalar x τ) τ =
      hard_threshold_scalar x τ := by
  by_cases h : |x| < τ
  · simp only [hard_threshold_scalar, h, ↓reduceIte, abs_zero, ite_self]
  · simp only [hard_threshold_scalar, h, ↓reduceIte]

omit [Fintype ι] in
/-- Hard-thresholding is idempotent coordinate-wise on vectors. -/
theorem hard_threshold_idempotent (w : W ι) (τ : ℝ) :
    hard_threshold (hard_threshold w τ) τ = hard_threshold w τ := by
  ext i
  simp only [
    hard_threshold,
    WithLp.equiv_apply,
    WithLp.equiv_symm_apply,
    hard_threshold_scalar_idempotent
  ]

/-- Hard-thresholding is not globally Lipschitz for positive thresholds. -/
theorem hard_threshold_scalar_not_lipschitz (τ : ℝ) (hτ : 0 < τ) :
    ∀ K : NNReal, ¬ LipschitzWith K (fun x : ℝ => hard_threshold_scalar x τ) := by
  intro K hLip
  let k : ℝ := (K : ℝ)
  let δ : ℝ := τ / (2 * (k + 1))
  have hk_nonneg : 0 ≤ k := by exact_mod_cast K.2
  have hk1_pos : 0 < k + 1 := by linarith
  have hden_pos : 0 < 2 * (k + 1) := by nlinarith [hk1_pos]
  have hδ_pos : 0 < δ := by
    unfold δ
    exact div_pos hτ hden_pos
  have hδ_lt : δ < τ := by
    unfold δ
    have hden_gt_one : 1 < 2 * (k + 1) := by nlinarith [hk_nonneg]
    have hmul : τ < τ * (2 * (k + 1)) := by nlinarith [hτ, hden_gt_one]
    exact (div_lt_iff₀ hden_pos).2 hmul
  let x0 : ℝ := τ - δ
  have hx0_abs_lt : |x0| < τ := by
    have hx0_pos : 0 < x0 := by
      unfold x0
      linarith
    have hx0_lt : x0 < τ := by
      unfold x0
      linarith
    rw [abs_of_pos hx0_pos]
    exact hx0_lt
  have hτ_not_lt : ¬ |τ| < τ := by
    rw [abs_of_pos hτ]
    exact lt_irrefl τ
  have hx_eval : hard_threshold_scalar x0 τ = 0 := by
    simp only [hard_threshold_scalar, hx0_abs_lt, ↓reduceIte]
  have hτ_eval : hard_threshold_scalar τ τ = τ := by
    simp only [hard_threshold_scalar, hτ_not_lt, ↓reduceIte]
  have hbound := hLip.norm_sub_le x0 τ
  rw [hx_eval, hτ_eval] at hbound
  have hnorm_right : ‖x0 - τ‖ = δ := by
    have hx0_sub : x0 - τ = -δ := by
      unfold x0
      ring
    rw [hx0_sub, norm_neg, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hδ_pos)]
  have hbound' : τ ≤ k * δ := by
    have hleft : ‖(0 : ℝ) - τ‖ = τ := by
      simp only [zero_sub, norm_neg, Real.norm_eq_abs, abs_of_pos hτ]
    have : ‖(0 : ℝ) - τ‖ ≤ (K : ℝ) * ‖x0 - τ‖ := hbound
    rw [hleft, hnorm_right] at this
    simpa only [ge_iff_le] using this
  have hkδ_lt : k * δ < τ := by
    unfold δ
    have hmul : k * (τ / (2 * (k + 1))) = τ * (k / (2 * (k + 1))) := by
      ring
    rw [hmul]
    have hk_div_lt_one' : k / (2 * (k + 1)) < 1 := by
      rw [div_lt_iff₀ hden_pos]
      nlinarith [hk_nonneg]
    have : τ * (k / (2 * (k + 1))) < τ * 1 := by
      exact mul_lt_mul_of_pos_left hk_div_lt_one' hτ
    simpa only [gt_iff_lt, mul_one] using this
  linarith

end LeanSharp
