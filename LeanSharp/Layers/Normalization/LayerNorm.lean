/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Core.Stats

/-!
# Normalization Layers

This module formalizes normalization layers, specifically Layer Normalization.

## Main definitions

* `layer_norm`: The Layer Normalization operation.
* `NormParam`: Parameter index type for scale (gamma) and shift (beta).
-/

namespace LeanSharp

variable {ι : Type} [Fintype ι]

/-- The parameter index type for normalization: scale (gamma) and shift (beta). -/
abbrev NormParam (ι : Type) := ι ⊕ ι

/-- Layer Normalization forward pass: y = γ * (x - μ) / σ + β.
    Note: We assume σ > 0 for the formal definition. -/
noncomputable def layernorm_forward (w : W (NormParam ι)) (x : W ι) : W ι :=
  let μ := vectorMean x
  let σ := vectorStd x
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    let x_i := (WithLp.equiv 2 (ι → ℝ) x) i
    let γ_i := (WithLp.equiv 2 _ w) (Sum.inl i)
    let β_i := (WithLp.equiv 2 _ w) (Sum.inr i)
    γ_i * ((x_i - μ) / σ) + β_i

/-- Layer Normalization backward pass. -/
noncomputable def layernorm_backward (w : W (NormParam ι)) (x : W ι) (g_out : W ι) :
    W (NormParam ι) × W ι :=
  let μ := vectorMean x
  let σ := vectorStd x
  let g_w := WithLp.equiv 2 _ |>.symm fun
    | Sum.inl i => (WithLp.equiv 2 _ g_out) i * (((WithLp.equiv 2 _ x) i - μ) / σ)
    | Sum.inr i => (WithLp.equiv 2 _ g_out) i
  -- Simplified gradient w.r.t input for the formal structure
  let g_x := WithLp.equiv 2 _ |>.symm fun i =>
    (WithLp.equiv 2 _ w) (Sum.inl i) * (WithLp.equiv 2 _ g_out) i / σ
  (g_w, g_x)

/-- Layer Normalization Layer instance. -/
noncomputable def layer_norm (ι : Type) [Fintype ι] : Layer (W ι) (W ι) where
  ParamDim := NormParam ι
  fintypeParamDim := inferInstance
  forward := layernorm_forward
  backward := layernorm_backward

end LeanSharp
