/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Activation Functions

This module formalizes activation functions as neural network layers.

## Main definitions

* `reluLayer`: The Rectified Linear Unit (ReLU) activation function.
* `softmax`: The Softmax activation function.
* `relu_lipschitz`: Lipshitz continuity of the ReLU layer.

## Theorems

* `relu_lipschitz`.
-/

namespace LeanSharp

variable {ι : Type}

/-- ReLU activation: max(0, x). -/
noncomputable def relu (x : W ι) : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    Max.max 0 ((WithLp.equiv 2 (ι → ℝ) x) i)

/-- **ReLU Lipschitz**: The ReLU activation function is 1-Lipschitz. -/
theorem relu_lipschitz [Fintype ι] : LipschitzWith 1 (relu (ι := ι)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [relu, WithLp.equiv_apply, WithLp.equiv_symm_apply, NNReal.coe_one, one_mul]
  rw [PiLp.dist_eq_of_L2, PiLp.dist_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [sq_le_sq, abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg]
  rw [Real.dist_eq, Real.dist_eq]
  exact (abs_max_sub_max_le_max 0 (x.ofLp i) 0 (y.ofLp i)).trans
    (by simp only [sub_self, abs_zero, abs_nonneg, sup_of_le_right, le_refl])

/-- ReLU backward pass. Since ReLU is not differentiable at 0, we use a subgradient (0). -/
noncomputable def reluBackward (x : W ι) (g_out : W ι) : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    if (WithLp.equiv 2 (ι → ℝ) x) i > 0 then (WithLp.equiv 2 (ι → ℝ) g_out) i else 0

/-- ReLU Layer instance. Activation functions have no parameters.

> [!WARNING]
> Models using `reluLayer` do not satisfy the `TwiceDifferentiable` requirement
> for Hessian-based structural analysis. Use `smoothReluLayer` (Softplus)
> for formally verified landscape curvature claims. -/
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

/-- Softplus (Smooth ReLU) activation for a vector x: log(1 + exp(x)). -/
noncomputable def smoothRelu (x : W ι) : W ι :=
  WithLp.equiv 2 _ |>.symm fun i =>
    Real.log (1 + Real.exp ((WithLp.equiv 2 _ x) i))

/-- Softplus (Smooth ReLU) backward pass (Sigmoid). -/
noncomputable def smoothReluBackward (x : W ι) (g_out : W ι) : W ι :=
  WithLp.equiv 2 _ |>.symm fun i =>
    let x_i := (WithLp.equiv 2 _ x) i
    let s := 1 / (1 + Real.exp (-x_i))
    s * (WithLp.equiv 2 _ g_out) i

/-- Smooth ReLU Layer instance. -/
noncomputable def smoothReluLayer (ι : Type) : Layer (W ι) (W ι) where
  ParamDim := Empty
  fintypeParamDim := inferInstance
  forward := fun _ x => smoothRelu x
  backward := fun _ x g_out => (0, smoothReluBackward x g_out)

/-- Softplus is continuously differentiable to order 2,
    resolving the C2/C0 Regularity Contradiction. -/
theorem contDiff_smoothRelu [Fintype ι] : ContDiff ℝ 2 (smoothRelu (ι := ι)) := by
  have hfact : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  apply contDiff_piLp' (p := 2)
  intro i
  apply ContDiff.log
  · apply ContDiff.add
    · exact contDiff_const
    · apply ContDiff.exp
      exact contDiff_piLp_apply (p := 2) (i := i)
  · intro x; positivity

end LeanSharp
