/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models

namespace LeanSharp

/-!
# Residual Layers

This module formalizes residual skip-connections $y = x + f(x)$.
Residual blocks are essential for training deep architectures by mitigating
gradient vanishing.

## Main definitions

* `residual_layer`: A wrapper that adds a skip connection to an existing layer.
-/

/-- A Residual Block is a wrapper that adds a skip connection: $y = x + f(x)$.
    The input and output spaces must be the same Euclidean space. -/
noncomputable def residual_layer {ι : Type} [Fintype ι] (f : Layer (W ι) (W ι)) :
    Layer (W ι) (W ι) where
  ParamDim := f.ParamDim
  fintypeParamDim := f.fintypeParamDim
  forward w x := x + f.forward w x
  backward w x g_out :=
    let (g_w, g_x_inner) := f.backward w x g_out
    -- The gradient of y = x + f(x) w.r.t x is (I + J_f)ᵀ g_out = g_out + J_fᵀ g_out.
    (g_w, g_out + g_x_inner)

end LeanSharp
