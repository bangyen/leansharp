/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Layers.Basic.Dropout
import LeanSharp.Layers.Specialized.Quantization
import LeanSharp.Layers.Architectures.Transformer
import LeanSharp.Layers.Architectures.ViT
import LeanSharp.Layers.Basic.Activation
import LeanSharp.Layers.Normalization.Normalization
import LeanSharp.Layers.Architectures.Attention
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Layers.Specialized.Convolution
import LeanSharp.Layers.Normalization.BatchNormalization
import LeanSharp.Layers.Basic.Residual
import LeanSharp.Core.Models
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LeanSharp.Tests

/-! ### Architectural Block Dimension Tests -/

/-- Test: Dropout Layer Parameter Dimensions. -/
example (ι : Type) [Fintype ι] (p : ℝ) :
    (dropout_layer ι p).ParamDim = ι := by
  rfl

/-- Test: Transformer MLP Block Parameter Dimensions. -/
example (S D D_ff : ℕ) [NeZero S] [NeZero D] :
    (transformer_mlp_block S D D_ff).ParamDim =
    ((NormParam (Fin D)) ⊕ (Fin D × Fin D_ff) ⊕ (Fin D_ff × Fin D)) := by
  rfl

/-- Test: Patch Embedding Layer Parameter Dimensions. -/
example (nc nh nw np ns nd : ℕ) [NeZero nh] [NeZero nw] :
    (patch_embedding nc nh nw np ns nd).ParamDim =
    ((Fin nc × Fin np × Fin np) × Fin nd) := by
  rfl

/-! ### Behavioral Tests -/

/-- Test: Linear layer output is zero when weights and biases are zero. -/
theorem test_linear_zero {ι_in ι_out : Type} [Fintype ι_in] (x : W ι_in) :
    linear_forward (0 : W (LinearParam ι_in ι_out)) x = 0 := by
  unfold linear_forward
  ext i
  simp

/-- Test: BatchNorm output is zero when γ=0 and β=0. -/
theorem test_batchnorm_zero {N D : ℕ} (x : W (Fin N × Fin D)) :
    batchnorm_forward (0 : W (NormParam (Fin D))) x = 0 := by
  unfold batchnorm_forward
  ext p
  simp

/-- Test: Conv2D output is zero when weights and bias are zero. -/
theorem test_conv2d_zero {h w kh kw : ℕ} {h_h : kh ≤ h} {h_w : kw ≤ w} (x : W (Fin h × Fin w)) :
    conv2d_forward h w kh kw h_h h_w (0 : W (ConvParam kh kw)) x = 0 := by
  unfold conv2d_forward
  ext p
  simp

/-- Test: Residual skip connection y = x + f(x). -/
theorem test_residual_forward {ι : Type} [Fintype ι] (f : Layer (W ι) (W ι)) (w : W f.ParamDim)
    (x : W ι) : (residual_layer f).forward w x = x + f.forward w x := by
  rfl

/-- Test: ReLU forward pass is max(0, x). -/
theorem test_relu_forward {ι : Type} (x : W ι) (i : ι) :
    (WithLp.equiv 2 _ (relu x)) i = Max.max 0 ((WithLp.equiv 2 _ x) i) := by
  unfold relu
  simp

/-- Test: LayerNorm output is zero when γ=0 and β=0. -/
theorem test_layernorm_zero {ι : Type} [Fintype ι] (x : W ι) :
    layernorm_forward (0 : W (NormParam ι)) x = 0 := by
  unfold layernorm_forward
  ext i
  simp

/-- Test: MHA output is zero when all projections are zero. -/
theorem test_mha_zero {S D : ℕ} (x : W (Fin S × Fin D)) :
    (mha_layer S D).forward 0 x = 0 := by
  unfold mha_layer
  dsimp [Layer.forward]
  unfold attention_forward
  ext p
  simp

/-- Test: Linear backward pass returns zero gradients when output gradient is zero. -/
theorem test_linear_backward_zero {ι_in ι_out : Type} [Fintype ι_out]
    (w : W (LinearParam ι_in ι_out)) (x : W ι_in) :
    linear_backward w x 0 = (0, 0) := by
  unfold linear_backward
  apply Prod.ext
  · ext p; cases p <;> simp
  · ext p; simp

/-- Test: BatchNorm backward pass returns zero gradients when output gradient is zero. -/
theorem test_batchnorm_backward_zero {N D : ℕ} (w : W (NormParam (Fin D))) (x : W (Fin N × Fin D)) :
    batchnorm_backward w x 0 = (0, 0) := by
  unfold batchnorm_backward
  apply Prod.ext
  · ext p; cases p <;> simp
  · ext p; simp

/-- Test: Chain composition forward pass for a 2-layer sequence (Linear + ReLU). -/
theorem test_chain_composition_forward {ι_in ι_out : Type} [Fintype ι_in] [Fintype ι_out]
    (w_l : W (LinearParam ι_in ι_out)) (x : W ι_in) :
    let l1 := linear_layer ι_in ι_out
    let l2 := relu_layer ι_out
    let p := ChainData.append (ChainData.single l1 w_l) (0 : W l2.ParamDim)
    forward_chain p x = relu (linear_forward w_l x) := by
  dsimp [forward_chain, relu_layer, linear_layer]
  rfl

end LeanSharp.Tests
