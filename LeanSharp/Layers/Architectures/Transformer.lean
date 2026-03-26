/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Layers.Architectures.Attention
import LeanSharp.Layers.Basic.Activation
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Layers.Basic.Residual
import LeanSharp.Layers.Normalization.LayerNorm
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LeanSharp

/-!
# Transformer Block

This module formalizes a full Transformer Encoder block.
It includes:
1. Positional Encoding (Sinusoidal).
2. Feature-wise Layer Normalization.
3. Multi-Head Attention skip-connection.
4. MLP (Feed-Forward) skip-connection.

## Main definitions

* `posEncoding`: Sinusoidal positional embeddings.
* `feature_norm`: Normalization across the feature dimension.
* `transformer_encoder`: A full encoder block composition.
-/

variable {S D : ℕ} [NeZero S] [NeZero D]

/-- Sinusoidal Positional Encoding. -/
noncomputable def posEncoding (S D : ℕ) : W (Fin S × Fin D) :=
  WithLp.equiv 2 _ |>.symm fun (s, d) =>
    let pos := (s : ℝ)
    let dim := (d : ℝ)
    let model_dim := (D : ℝ)
    if (d : ℕ) % 2 = 0 then
      Real.sin (pos / (10000 ^ (dim / model_dim)))
    else
      Real.cos (pos / (10000 ^ ((dim - 1) / model_dim)))

/-- Feature-wise Layer Normalization forward pass. -/
noncomputable def featureNormForward (w : W (NormParam (Fin D))) (x : W (Fin S × Fin D)) :
    W (Fin S × Fin D) :=
  WithLp.equiv 2 _ |>.symm fun (s, d) =>
    let x_f := WithLp.equiv 2 _ x
    let row := WithLp.equiv 2 _ |>.symm fun d' => x_f (s, d')
    (WithLp.equiv 2 _ (layernormForward w row)) d

/-- Feature-wise Layer Normalization backward pass. -/
noncomputable def featureNormBackward (w : W (NormParam (Fin D))) (x : W (Fin S × Fin D))
    (g_out : W (Fin S × Fin D)) : W (NormParam (Fin D)) × W (Fin S × Fin D) :=
  let x_f := WithLp.equiv 2 _ x
  let g_out_f := WithLp.equiv 2 _ g_out
  -- Compute row-wise gradients and sum them
  let g_row (s : Fin S) : W (NormParam (Fin D)) × W (Fin D) :=
    let row := WithLp.equiv 2 _ |>.symm fun d' => x_f (s, d')
    let g_out_row := WithLp.equiv 2 _ |>.symm fun d' => g_out_f (s, d')
    layernormBackward w row g_out_row
  let g_w_sum := ∑ s, (g_row s).1
  let g_x := WithLp.equiv 2 _ |>.symm fun (s, d) =>
    (WithLp.equiv 2 _ (g_row s).2) d
  (g_w_sum, g_x)

/-- The Attention Block: Residual(LN + MHA) -/
noncomputable def transformerAttnBlock (S D : ℕ) :
    Layer (W (Fin S × Fin D)) (W (Fin S × Fin D)) where
  ParamDim := (NormParam (Fin D)) ⊕ (ATTParam (Fin D))
  fintypeParamDim := inferInstance
  forward w x :=
    let w_f := WithLp.equiv 2 _ w
    let w_ln := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inl i))
    let w_mha := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inr i))
    let ln := featureNormForward w_ln x
    let attn := (mhaLayer S D).forward w_mha ln
    x + attn
  backward w x g_out :=
    let w_f := WithLp.equiv 2 _ w
    let w_ln := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inl i))
    let w_mha := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inr i))
    let ln := featureNormForward w_ln x
    let (g_w_mha, g_ln) := (mhaLayer S D).backward w_mha ln g_out
    let (g_w_ln, g_x_ln) := featureNormBackward w_ln x g_ln
    let g_w := WithLp.equiv 2 _ |>.symm fun
      | Sum.inl i => (WithLp.equiv 2 _ g_w_ln) i
      | Sum.inr i => (WithLp.equiv 2 _ g_w_mha) i
    (g_w, g_out + g_x_ln)

/-- The MLP Block: Residual(LN + Linear + ReLU + Linear) -/
noncomputable def transformerMlpBlock (S D D_ff : ℕ) :
    Layer (W (Fin S × Fin D)) (W (Fin S × Fin D)) where
  ParamDim := (NormParam (Fin D)) ⊕ (Fin D × Fin D_ff) ⊕ (Fin D_ff × Fin D)
  fintypeParamDim := inferInstance
  forward w x :=
    let w_f := WithLp.equiv 2 _ w
    let w_ln := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inl i))
    let w_l1_vec := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inr (Sum.inl i)))
    let w_l2_vec := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inr (Sum.inr i)))
    let ln := featureNormForward w_ln x
    let x_ln_f := WithLp.equiv 2 _ ln
    let w1_f := WithLp.equiv 2 _ w_l1_vec
    let w2_f := WithLp.equiv 2 _ w_l2_vec
    let mlp1 := WithLp.equiv 2 (Fin S × Fin D_ff → ℝ) |>.symm fun (s, df) =>
      ∑ d, x_ln_f (s, d) * w1_f (d, df)
    let relu := WithLp.equiv 2 _ |>.symm fun p =>
      let val := (WithLp.equiv 2 _ mlp1) p
      if val > 0 then val else 0
    let mlp2 := WithLp.equiv 2 (Fin S × Fin D → ℝ) |>.symm fun (s, d) =>
      ∑ df, (WithLp.equiv 2 _ relu) (s, df) * w2_f (df, d)
    x + mlp2
  backward w x g_out :=
    let w_f := WithLp.equiv 2 _ w
    let w1_f := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inr (Sum.inl i)))
    let w2_f := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inr (Sum.inr i)))
    let w_ln := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inl i))
    -- Recompute intermediate activations
    let ln := featureNormForward w_ln x
    let x_ln_f := WithLp.equiv 2 _ ln
    let w1_vec_f := WithLp.equiv 2 _ w1_f
    let w2_vec_f := WithLp.equiv 2 _ w2_f
    let mlp1_f := fun (s : Fin S) (df : Fin D_ff) => ∑ d, x_ln_f (s, d) * w1_vec_f (d, df)
    let relu_f := fun (s : Fin S) (df : Fin D_ff) => if mlp1_f s df > 0 then mlp1_f s df else 0
    -- Backward pass for mlp2
    let g_out_f := WithLp.equiv 2 _ g_out
    let g_relu_f := fun (s : Fin S) (df : Fin D_ff) => ∑ d, g_out_f (s, d) * w2_vec_f (df, d)
    let g_w2 := fun (df : Fin D_ff) (d : Fin D) => ∑ s, g_out_f (s, d) * relu_f s df
    -- Backward pass for relu
    let g_mlp1_f := fun (s : Fin S) (df : Fin D_ff) => if mlp1_f s df > 0 then g_relu_f s df else 0
    -- Backward pass for mlp1
    let g_ln_f := fun (s : Fin S) (d : Fin D) => ∑ df, g_mlp1_f s df * w1_vec_f (d, df)
    let g_w1 := fun (d : Fin D) (df : Fin D_ff) => ∑ s, g_mlp1_f s df * x_ln_f (s, d)
    -- Backward pass for LayerNorm
    let g_ln := WithLp.equiv 2 _ |>.symm fun p => g_ln_f p.1 p.2
    let (g_w_ln_vec, g_x_ln) := featureNormBackward w_ln x g_ln
    let g_w := WithLp.equiv 2 _ |>.symm fun
      | Sum.inl i => (WithLp.equiv 2 _ g_w_ln_vec) i
      | Sum.inr (Sum.inl i) => g_w1 i.1 i.2
      | Sum.inr (Sum.inr i) => g_w2 i.1 i.2
    (g_w, g_out + g_x_ln)

/-- A full Transformer Encoder Block (composed of Attn + MLP blocks). -/
noncomputable def transformerEncoderBlock (S D D_ff : ℕ) :
    Chain (W (Fin S × Fin D)) (W (Fin S × Fin D)) :=
  let attn := transformerAttnBlock S D
  let mlp := transformerMlpBlock S D D_ff
  Chain.append (Chain.single attn) mlp

end LeanSharp
