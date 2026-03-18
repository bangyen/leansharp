/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LeanSharp

/-!
# Weight Pruning and Quantization

This module formalizes weight pruning and quantization mappings,
along with theorems regarding their stability.

## Main definitions

* `prune_weights`: Zeros out weights below a threshold.
* `uniform_quantize`: Maps weights to the nearest level in a grid.

## Theorems

* `pruning_error_bound`.
* `pruning_forward_stability`.
* `uniform_quantize_error_bound`.
* `quantization_forward_stability`.
-/

variable {ι : Type*} [Fintype ι]

/-- Pruning operator: Zeros out weights with absolute value < ε. -/
noncomputable def prune_weights (ε : ℝ) (w : W ι) : W ι :=
  (WithLp.equiv 2 _).symm fun i =>
    let val := (WithLp.equiv 2 _ w) i
    if |val| < ε then 0 else val

/-- Uniform Quantization: Maps a value to the nearest Level * step. -/
noncomputable def uniform_quantize (step : ℝ) (w : W ι) : W ι :=
  if step = 0 then w else
  (WithLp.equiv 2 _).symm fun i =>
    let val := (WithLp.equiv 2 _ w) i
    (round (val / step) : ℝ) * step

/-- **Pruning Bound**: The squared difference between a weight and its pruned version
    is bounded by the number of pruned elements times ε^2. -/
theorem pruning_error_bound (ε : ℝ) (w : W ι) :
    ‖w - prune_weights ε w‖^2 ≤ (Fintype.card ι : ℝ) * ε^2 := by
  -- Convert norm squared difference into a sum
  rw [EuclideanSpace.norm_sq_eq]
  let pruned := prune_weights ε w
  have h_bound (i : ι) : ‖(w - pruned).ofLp i‖^2 ≤ ε^2 := by
    dsimp only [
      prune_weights,
      WithLp.equiv_apply,
      Lean.Elab.WF.paramLet,
      WithLp.equiv_symm_apply,
      PiLp.sub_apply,
      Real.norm_eq_abs,
      pruned
    ]
    -- Pointwise subtraction
    split_ifs with h
    · rw [sub_zero, sq_abs]
      by_cases hε : 0 ≤ ε
      · apply sq_le_sq.mpr
        rw [abs_of_nonneg hε]
        exact h.le
      · have hεle : ε ≤ 0 := le_of_not_ge hε
        have hFalse : False := by
          nlinarith [abs_nonneg (w.ofLp i), h, hεle]
        exact False.elim hFalse
    · rw [sub_self, abs_zero, zero_pow (by norm_num)]
      exact sq_nonneg ε
  -- Use sum_le_sum with an explicit type to avoid metavariables
  refine (@Finset.sum_le_sum ι ℝ _ _ (fun i => ‖(w - pruned).ofLp i‖^2)
    (fun _ => ε^2) Finset.univ _ ?_).trans ?_
  · intro i _
    exact h_bound i
  · rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- **Pruning Stability**: If a layer's forward pass is Lipschitz in its weights,
    the output error due to pruning is bounded. -/
theorem pruning_forward_stability {ι_in ι_out : Type} [Fintype ι_out]
    (f : Layer (W ι_in) (W ι_out)) (w : W f.ParamDim) (x : W ι_in) (ε : ℝ)
    (h_lip : LipschitzWith K (fun w' => f.forward w' x)) :
    ‖f.forward w x - f.forward (prune_weights ε w) x‖ ≤
    K * (Real.sqrt (Fintype.card f.ParamDim) * |ε|) := by
  have h_diff := h_lip.norm_sub_le w (prune_weights ε w)
  apply h_diff.trans
  have h_sq := pruning_error_bound ε w
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  -- Normalize the square root of the bound
  rw [Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs] at h_sqrt
  -- Apply monotonicity
  apply mul_le_mul_of_nonneg_left h_sqrt (by positivity)

/-- **Quantization Bound**: The squared difference between a weight and its
quantized version is bounded by the number of elements times `(|step|/2)^2`.
This formulation is sign-robust and also covers the degenerate `step = 0` case. -/
theorem uniform_quantize_error_bound (step : ℝ) (w : W ι) :
    ‖w - uniform_quantize step w‖^2 ≤ (Fintype.card ι : ℝ) * (|step| / 2)^2 := by
  by_cases h_step0 : step = 0
  · subst h_step0
    simp only [
      uniform_quantize,
      ↓reduceIte,
      sub_self,
      norm_zero,
      ne_eq,
      OfNat.ofNat_ne_zero,
      not_false_eq_true,
      zero_pow,
      abs_zero,
      zero_div,
      mul_zero,
      le_refl
    ]
  · let quantized := uniform_quantize step w
    rw [EuclideanSpace.norm_sq_eq]
    refine (@Finset.sum_le_sum ι ℝ _ _ (fun i => ‖(w - quantized).ofLp i‖^2)
      (fun _ => (|step| / 2)^2) Finset.univ _ ?_).trans ?_
    · intro i _
      dsimp only [PiLp.sub_apply, Real.norm_eq_abs]
      simp only [quantized, uniform_quantize, h_step0, if_false]
      let x := (WithLp.equiv 2 (ι → ℝ) w) i
      change |x - round (x / step) * step| ^ 2 ≤ (|step| / 2) ^ 2
      have h_rw : x - round (x / step) * step = step * (x / step - round (x / step)) := by
        rw [mul_sub, mul_div_cancel₀ _ h_step0, mul_comm step]
      rw [h_rw, abs_mul, mul_pow, sq_abs]
      have h_step_sq : step ^ 2 = |step| ^ 2 := by
        rw [← sq_abs]
      rw [h_step_sq]
      have h_le : |x / step - round (x / step)| ^ 2 ≤ (1 / 2) ^ 2 := by
        have h_abs := abs_sub_round (x / step)
        apply sq_le_sq.mpr
        rw [abs_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
        exact h_abs
      rw [show (|step| / 2) ^ 2 = (1 / 2) ^ 2 * |step| ^ 2 by ring, mul_comm]
      exact mul_le_mul_of_nonneg_right h_le (sq_nonneg |step|)
    · rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- **Quantization Stability**: Forward pass error due to quantization is bounded
    by the Lipschitz constant times the quantization error. -/
theorem quantization_forward_stability {ι_in ι_out : Type} [Fintype ι_out]
    (f : Layer (W ι_in) (W ι_out)) (w : W f.ParamDim) (x : W ι_in) (step : ℝ)
    (h_lip : LipschitzWith K (fun w' => f.forward w' x)) :
    ‖f.forward w x - f.forward (uniform_quantize step w) x‖ ≤
    K * (Real.sqrt (Fintype.card f.ParamDim) * (|step| / 2)) := by
  have h_diff := h_lip.norm_sub_le w (uniform_quantize step w)
  apply h_diff.trans
  have h_sq := uniform_quantize_error_bound step w
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at h_sqrt
  apply mul_le_mul_of_nonneg_left h_sqrt (by positivity)

end LeanSharp
