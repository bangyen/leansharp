/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Core.Stats
import LeanSharp.Layers.Normalization.Normalization

namespace LeanSharp

/-!
# Batch Normalization

This module formalizes Batch Normalization for 2D inputs (Batch × Features).
Normalization is performed across the batch dimension.

## Main definitions

* `batch_norm_layer`: The Batch Normalization operation.
-/

/-- Batch mean for a specific feature dimension `d`. -/
noncomputable def batch_mean {N D : ℕ} (x : W (Fin N × Fin D)) (d : Fin D) : ℝ :=
  (∑ n : Fin N, (WithLp.equiv 2 _ x) (n, d)) / N

/-- Batch variance for a specific feature dimension `d`. -/
noncomputable def batch_var {N D : ℕ} (x : W (Fin N × Fin D)) (d : Fin D) (μ : Fin D → ℝ) : ℝ :=
  (∑ n : Fin N, ((WithLp.equiv 2 _ x) (n, d) - μ d)^2) / N

/-- Batch Normalization forward pass. -/
noncomputable def batchnorm_forward {N D : ℕ}
    (w : W (NormParam (Fin D))) (x : W (Fin N × Fin D)) :
    W (Fin N × Fin D) :=
  let μ := fun d => batch_mean x d
  let σ := fun d => Real.sqrt (batch_var x d μ + 0.00001)
  WithLp.equiv 2 (Fin N × Fin D → ℝ) |>.symm fun p =>
    let (n, d) := p
    let x_nd := (WithLp.equiv 2 _ x) (n, d)
    let γ_d := (WithLp.equiv 2 _ w) (Sum.inl d)
    let β_d := (WithLp.equiv 2 _ w) (Sum.inr d)
    γ_d * ((x_nd - μ d) / σ d) + β_d

/-- Batch Normalization backward pass. -/
noncomputable def batchnorm_backward {N D : ℕ}
    (w : W (NormParam (Fin D))) (x : W (Fin N × Fin D))
    (g_out : W (Fin N × Fin D)) : W (NormParam (Fin D)) × W (Fin N × Fin D) :=
  let μ := fun d => batch_mean x d
  let σ := fun d => Real.sqrt (batch_var x d μ + 0.00001)
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
noncomputable def batch_norm_layer (N D : ℕ) :
    Layer (W (Fin N × Fin D)) (W (Fin N × Fin D)) where
  ParamDim := NormParam (Fin D)
  fintypeParamDim := inferInstance
  forward := batchnorm_forward
  backward := batchnorm_backward

end LeanSharp
