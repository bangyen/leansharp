/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models

/-!
# Activation Functions

This module formalizes activation functions as neural network layers.

## Main definitions

* `reluLayer`: The Rectified Linear Unit (ReLU) activation function.
* `softmax`: The Softmax activation function.
-/

namespace LeanSharp

variable {ι : Type}

/-- ReLU activation: max(0, x). -/
noncomputable def relu (x : W ι) : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    Max.max 0 ((WithLp.equiv 2 (ι → ℝ) x) i)

/-- ReLU backward pass. Since ReLU is not differentiable at 0, we use a subgradient (0). -/
noncomputable def reluBackward (x : W ι) (g_out : W ι) : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    if (WithLp.equiv 2 (ι → ℝ) x) i > 0 then (WithLp.equiv 2 (ι → ℝ) g_out) i else 0

/-- ReLU Layer instance. Activation functions have no parameters. -/
noncomputable def reluLayer (ι : Type) : Layer (W ι) (W ι) where
  ParamDim := Empty
  fintypeParamDim := inferInstance
  forward := fun _ x => relu x
  backward := fun _ x g_out => (0, reluBackward x g_out)

/-- Softmax activation for a vector x. -/
noncomputable def softmax [Fintype ι] (x : W ι) : W ι :=
  let x_f := WithLp.equiv 2 _ x
  let exps := fun i => Real.exp (x_f i)
  let sum_exps := ∑ i, exps i
  WithLp.equiv 2 _ |>.symm fun i =>
    exps i / sum_exps

/-- Softmax backward pass.
    The Jacobian is J_ij = s_i (δ_ij - s_j). -/
noncomputable def softmaxBackward [Fintype ι] (x : W ι) (g_out : W ι) : W ι :=
  let s := softmax x
  let s_f := WithLp.equiv 2 _ s
  let g_out_f := WithLp.equiv 2 _ g_out
  let sum_sg := ∑ i, s_f i * g_out_f i
  WithLp.equiv 2 _ |>.symm fun i =>
    s_f i * (g_out_f i - sum_sg)

/-- Softmax Layer instance. -/
noncomputable def softmaxLayer (ι : Type) [Fintype ι] : Layer (W ι) (W ι) where
  ParamDim := Empty
  fintypeParamDim := inferInstance
  forward := fun _ x => softmax x
  backward := fun _ x g_out => (0, softmaxBackward x g_out)

end LeanSharp
