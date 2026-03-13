/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models

/-!
# Linear Layers

This module formalizes linear (affine) layers $y = Wx + b$ within the `Layer` framework.

## Main definitions

* `linear_layer`: A layer representing an affine transformation.
* `LinearParam`: The parameter index type for weights and biases.
-/

namespace LeanSharp

open BigOperators

variable {ι_in ι_out : Type} [Fintype ι_in] [Fintype ι_out]

/-- The parameter index type for a linear layer: (output_dim × input_dim) for weights,
and output_dim for biases. -/
abbrev LinearParam (ι_in ι_out : Type) := (ι_out × ι_in) ⊕ ι_out

instance [Fintype ι_in] [Fintype ι_out] : Fintype (LinearParam ι_in ι_out) :=
  inferInstance

/-- The forward pass $y = Wx + b$. -/
noncomputable def linear_forward (w : W (LinearParam ι_in ι_out)) (x : W ι_in) : W ι_out :=
  WithLp.equiv 2 (ι_out → ℝ) |>.symm fun i =>
    (∑ j, (WithLp.equiv 2 _ w) (Sum.inl (i, j)) * (WithLp.equiv 2 _ x) j) +
    (WithLp.equiv 2 _ w) (Sum.inr i)

/-- The backward pass for a linear layer.
    Returns (gradient w.r.t parameters, gradient w.r.t input). -/
noncomputable def linear_backward (w : W (LinearParam ι_in ι_out)) (x : W ι_in) (g_out : W ι_out) :
    W (LinearParam ι_in ι_out) × W ι_in :=
  let g_w := WithLp.equiv 2 _ |>.symm fun
    | Sum.inl (i, j) => (WithLp.equiv 2 _ g_out) i * (WithLp.equiv 2 _ x) j
    | Sum.inr i => (WithLp.equiv 2 _ g_out) i
  let g_x := WithLp.equiv 2 _ |>.symm fun j =>
    ∑ i, (WithLp.equiv 2 _ w) (Sum.inl (i, j)) * (WithLp.equiv 2 _ g_out) i
  (g_w, g_x)

/-- Construct a linear layer instance. -/
noncomputable def linear_layer (ι_in ι_out : Type) [Fintype ι_in] [Fintype ι_out] :
    Layer (W ι_in) (W ι_out) where
  ParamDim := LinearParam ι_in ι_out
  fintypeParamDim := inferInstance
  forward := linear_forward
  backward := linear_backward

end LeanSharp
