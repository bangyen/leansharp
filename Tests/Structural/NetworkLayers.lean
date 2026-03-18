/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Layers.Architectures.Attention
import LeanSharp.Layers.Architectures.Transformer
import LeanSharp.Layers.Architectures.VisionTransformer
import LeanSharp.Layers.Basic.Activation
import LeanSharp.Layers.Basic.Dropout
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Layers.Basic.Residual
import LeanSharp.Layers.Normalization.BatchNorm
import LeanSharp.Layers.Normalization.LayerNorm
import LeanSharp.Layers.Specialized.Convolution
import LeanSharp.Layers.Specialized.Quantization
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LeanSharp.Tests

/-!
# Layer Tests

This module collects regression tests for core layer and architecture behavior.

## Theorems

* Dimension checks for dropout, transformer MLP blocks, and patch embeddings.
* Behavioral checks for forward and backward passes of major layers.
-/

/-- Test: Dropout Layer Parameter Dimensions. -/
example (ι : Type) [Fintype ι] (p : ℝ) :
    (dropout_layer ι p).ParamDim = ι := by
  rfl

/-- Test: Transformer MLP Block Parameter Dimensions. -/
example (S D D_ff : ℕ) [NeZero S] [NeZero D] :
    (transformerMlpBlock S D D_ff).ParamDim =
    ((NormParam (Fin D)) ⊕ (Fin D × Fin D_ff) ⊕ (Fin D_ff × Fin D)) := by
  rfl

/-- Test: Patch Embedding Layer Parameter Dimensions. -/
example (nc nh nw np ns nd : ℕ) [NeZero nh] [NeZero nw] [NeZero np] [NeZero ns] :
    (patchEmbedding nc nh nw np ns nd).ParamDim =
    ((Fin nc × Fin np × Fin np) × Fin nd) := by
  rfl

-- Behavioral tests

/-- Test: Linear layer output is zero when weights and biases are zero. -/
theorem test_linear_zero {ι_in ι_out : Type} [Fintype ι_in] (x : W ι_in) :
    linear_forward (0 : W (LinearParam ι_in ι_out)) x = 0 := by
  unfold linear_forward
  ext i
  simp only [
    WithLp.equiv_apply,
    PiLp.zero_apply,
    zero_mul,
    Finset.sum_const_zero,
    add_zero,
    WithLp.equiv_symm_apply
  ]

/-- Test: BatchNorm output is zero when γ=0 and β=0. -/
theorem test_batchnorm_zero {N D : ℕ} (x : W (Fin N × Fin D)) :
    batchnorm_forward (0 : W (NormParam (Fin D))) x = 0 := by
  unfold batchnorm_forward
  ext p
  simp only [
    WithLp.equiv_apply,
    PiLp.zero_apply,
    Prod.mk.eta,
    zero_mul,
    add_zero,
    WithLp.equiv_symm_apply
  ]

/-- Test: Conv2D output is zero when weights and bias are zero. -/
theorem test_conv2d_zero {h w kh kw : ℕ} {h_h : kh ≤ h} {h_w : kw ≤ w} (x : W (Fin h × Fin w)) :
    conv2d_forward h w kh kw h_h h_w (0 : W (ConvParam kh kw)) x = 0 := by
  unfold conv2d_forward
  ext p
  simp only [
    WithLp.equiv_apply,
    PiLp.zero_apply,
    zero_mul,
    Finset.sum_const_zero,
    add_zero,
    WithLp.equiv_symm_apply
  ]

/-- Test: Residual skip connection y = x + f(x). -/
theorem test_residual_forward {ι : Type} [Fintype ι] (f : Layer (W ι) (W ι)) (w : W f.ParamDim)
    (x : W ι) : (residual_layer f).forward w x = x + f.forward w x := by
  rfl

/-- Test: ReLU forward pass is max(0, x). -/
theorem test_relu_forward {ι : Type} (x : W ι) (i : ι) :
    (WithLp.equiv 2 _ (relu x)) i = Max.max 0 ((WithLp.equiv 2 _ x) i) := by
  unfold relu
  rw [
    WithLp.equiv_apply,
    WithLp.equiv_symm_apply
  ]

/-- Test: LayerNorm output is zero when γ=0 and β=0. -/
theorem test_layernorm_zero {ι : Type} [Fintype ι] (x : W ι) :
    layernorm_forward (0 : W (NormParam ι)) x = 0 := by
  unfold layernorm_forward
  ext i
  simp only [
    WithLp.equiv_apply,
    PiLp.zero_apply,
    zero_mul,
    add_zero,
    WithLp.equiv_symm_apply
  ]

/-- Test: MHA output is zero when all projections are zero. -/
theorem test_mha_zero {S D : ℕ} (x : W (Fin S × Fin D)) :
    (mha_layer S D).forward 0 x = 0 := by
  unfold mha_layer
  dsimp only [
    WithLp.equiv_apply,
    WithLp.equiv_symm_apply,
    Lean.Elab.WF.paramLet,
    PiLp.zero_apply
  ]
  unfold attention_forward
  ext p
  simp only [
    mul_zero,
    Finset.sum_const_zero,
    WithLp.equiv_apply,
    zero_div,
    WithLp.equiv_symm_apply,
    PiLp.zero_apply
  ]

/-- Test: Linear backward pass returns zero gradients when output gradient is zero. -/
theorem test_linear_backward_zero {ι_in ι_out : Type} [Fintype ι_out]
    (w : W (LinearParam ι_in ι_out)) (x : W ι_in) :
    linear_backward w x 0 = (0, 0) := by
  unfold linear_backward
  apply Prod.ext
  · ext p; cases p <;> simp only [
      WithLp.equiv_apply,
      PiLp.zero_apply,
      zero_mul,
      WithLp.equiv_symm_apply
    ]
  · ext p; simp only [
      WithLp.equiv_apply,
      PiLp.zero_apply,
      mul_zero,
      Finset.sum_const_zero,
      WithLp.equiv_symm_apply
    ]

/-- Test: BatchNorm backward pass returns zero gradients when output gradient is zero. -/
theorem test_batchnorm_backward_zero {N D : ℕ} (w : W (NormParam (Fin D))) (x : W (Fin N × Fin D)) :
    batchnorm_backward w x 0 = (0, 0) := by
  unfold batchnorm_backward
  apply Prod.ext
  · ext p; cases p <;> simp only [
      WithLp.equiv_apply,
      PiLp.zero_apply,
      zero_mul,
      Finset.sum_const_zero,
      WithLp.equiv_symm_apply
    ]
  · ext p; simp only [
      WithLp.equiv_apply,
      PiLp.zero_apply,
      mul_zero,
      zero_div,
      WithLp.equiv_symm_apply
    ]

/-- Test: Chain composition forward pass for a 2-layer sequence (Linear + ReLU). -/
theorem test_chain_composition_forward {ι_in ι_out : Type} [Fintype ι_in] [Fintype ι_out]
    (w_l : W (LinearParam ι_in ι_out)) (x : W ι_in) :
    let l1 := linear_layer ι_in ι_out
    let l2 := relu_layer ι_out
    let p := ChainData.append (ChainData.single l1 w_l) (0 : W l2.ParamDim)
    forward_chain p x = relu (linear_forward w_l x) := by
  dsimp only [
    linear_layer,
    relu_layer,
    forward_chain,
    Lean.Elab.WF.paramLet
  ]
  rfl

end LeanSharp.Tests
