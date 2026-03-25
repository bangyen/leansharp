/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Core.Stats
import LeanSharp.Layers.Normalization.LayerNorm

namespace LeanSharp

/-!
# Batch Normalization

This module formalizes Batch Normalization for 2D inputs (Batch × Features).
Normalization is performed across the batch dimension.

## Main definitions

* `batchNormLayer`: The Batch Normalization operation.

## Main theorems

* `batchnorm_mean_zero`: Proves that BatchNorm output has mean zero.
-/

/-- Batch mean for a specific feature dimension `d`. -/
noncomputable def batchMean {N D : ℕ} (x : W (Fin N × Fin D)) (d : Fin D) : ℝ :=
  (∑ n : Fin N, (WithLp.equiv 2 _ x) (n, d)) / N

/-- Batch variance for a specific feature dimension `d`. -/
noncomputable def batchVar {N D : ℕ} (x : W (Fin N × Fin D)) (d : Fin D)
    (μ : Fin D → ℝ) : ℝ :=
  (∑ n : Fin N, ((WithLp.equiv 2 _ x) (n, d) - μ d)^2) / N

/-- Batch Normalization forward pass. -/
noncomputable def batchnormForward {N D : ℕ}
    (w : W (NormParam (Fin D))) (x : W (Fin N × Fin D)) :
    W (Fin N × Fin D) :=
  let μ := fun d => batchMean x d
  let σ := fun d => Real.sqrt (batchVar x d μ)
  WithLp.equiv 2 (Fin N × Fin D → ℝ) |>.symm fun p =>
    let (n, d) := p
    let x_nd := (WithLp.equiv 2 _ x) (n, d)
    let γ_d := (WithLp.equiv 2 _ w) (Sum.inl d)
    let β_d := (WithLp.equiv 2 _ w) (Sum.inr d)
    γ_d * ((x_nd - μ d) / σ d) + β_d

/-- Batch Normalization backward pass. -/
noncomputable def batchnormBackward {N D : ℕ}
    (w : W (NormParam (Fin D))) (x : W (Fin N × Fin D))
    (g_out : W (Fin N × Fin D)) : W (NormParam (Fin D)) × W (Fin N × Fin D) :=
  let μ := fun d => batchMean x d
  let σ := fun d => Real.sqrt (batchVar x d μ)
  let g_w := WithLp.equiv 2 _ |>.symm fun
    | Sum.inl d => ∑ n : Fin N, (WithLp.equiv 2 _ g_out) (n, d) *
        (((WithLp.equiv 2 _ x) (n, d) - μ d) / σ d)
    | Sum.inr d => ∑ n : Fin N, (WithLp.equiv 2 _ g_out) (n, d)
  -- Simplified gradient w.r.t input for structural purposes
  let g_x := WithLp.equiv 2 _ |>.symm fun p =>
    let (_, d) := p
    ((WithLp.equiv 2 _ w) (Sum.inl d) * (WithLp.equiv 2 _ g_out) p) / σ d
  (g_w, g_x)

/-- Batch Normalization Layer instance. -/
noncomputable def batchNormLayer (N D : ℕ) :
    Layer (W (Fin N × Fin D)) (W (Fin N × Fin D)) where
  ParamDim := NormParam (Fin D)
  fintypeParamDim := inferInstance
  forward := batchnormForward
  backward := batchnormBackward

/-- **Mean Normalization**: For any input `x`, the batch mean of the normalized output
(with γ=1, β=0) is zero for all feature dimensions `d`. -/
theorem batchnorm_mean_zero {N D : ℕ} (hN : 0 < N) (x : W (Fin N × Fin D)) (d : Fin D) :
    let w_id : W (NormParam (Fin D)) :=
      WithLp.equiv 2 _ |>.symm fun | Sum.inl _ => 1 | Sum.inr _ => 0
    batchMean (batchnormForward w_id x) d = 0 := by
  unfold batchMean batchnormForward
  simp only [Equiv.apply_symm_apply, one_mul, add_zero]
  have hN_real : (N : ℝ) ≠ 0 := by positivity
  rw [← Finset.sum_div]
  have h_sum : ∑ n : Fin N, ((WithLp.equiv 2 _) x (n, d) - batchMean x d) = 0 := by
    unfold batchMean
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hN_real]
    simp only [sub_self, mul_zero]
  rw [h_sum]
  simp only [zero_div]

end LeanSharp
