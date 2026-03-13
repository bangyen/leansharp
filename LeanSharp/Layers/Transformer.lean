/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Layers.Attention
import LeanSharp.Layers.Linear
import LeanSharp.Layers.Normalization
import LeanSharp.Layers.Activation
import LeanSharp.Layers.Residual
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

* `pos_encoding`: Sinusoidal positional embeddings.
* `feature_norm`: Normalization across the feature dimension.
* `transformer_encoder`: A full encoder block composition.
-/

variable {S D : ℕ} [NeZero S] [NeZero D]

/-- Sinusoidal Positional Encoding. -/
noncomputable def pos_encoding (S D : ℕ) : W (Fin S × Fin D) :=
  WithLp.equiv 2 _ |>.symm fun (s, d) =>
    let pos := (s : ℝ)
    let dim := (d : ℝ)
    let model_dim := (D : ℝ)
    if (d : ℕ) % 2 = 0 then
      Real.sin (pos / (10000 ^ (dim / model_dim)))
    else
      Real.cos (pos / (10000 ^ ((dim - 1) / model_dim)))

/-- Feature-wise Layer Normalization. -/
noncomputable def feature_norm_forward (w : W (NormParam (Fin D))) (x : W (Fin S × Fin D)) : 
    W (Fin S × Fin D) :=
  WithLp.equiv 2 _ |>.symm fun (s, d) =>
    let x_f := WithLp.equiv 2 _ x
    let w_f := WithLp.equiv 2 _ w
    let row := fun d' => x_f (s, d')
    let μ_s := (∑ i, row i) / D
    let σ_s := Real.sqrt ((∑ i, (row i - μ_s)^2) / D + 0.00001)
    let γ_d := w_f (Sum.inl d)
    let β_d := w_f (Sum.inr d)
    γ_d * ((row d - μ_s) / σ_s) + β_d

/-- The Attention Block: Residual(LN + MHA) -/
noncomputable def transformer_attn_block (S D : ℕ) : 
    Layer (W (Fin S × Fin D)) (W (Fin S × Fin D)) where
  ParamDim := (NormParam (Fin D)) ⊕ (ATTParam (Fin D))
  fintypeParamDim := inferInstance
  forward w x :=
    let w_f := WithLp.equiv 2 _ w
    let w_ln := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inl i))
    let w_mha := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inr i))
    let ln := feature_norm_forward w_ln x
    let attn := (mha_layer S D).forward w_mha ln
    x + attn
  backward _ _ g_out := (0, g_out)

/-- The MLP Block: Residual(LN + Linear + ReLU + Linear) -/
noncomputable def transformer_mlp_block (S D D_ff : ℕ) : 
    Layer (W (Fin S × Fin D)) (W (Fin S × Fin D)) where
  ParamDim := (NormParam (Fin D)) ⊕ (Fin D × Fin D_ff) ⊕ (Fin D_ff × Fin D)
  fintypeParamDim := inferInstance
  forward w x :=
    let w_f := WithLp.equiv 2 _ w
    let w_ln := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inl i))
    let w_l1_vec := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inr (Sum.inl i)))
    let w_l2_vec := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inr (Sum.inr i)))
    
    let ln := feature_norm_forward w_ln x
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
  backward _ _ g_out := (0, g_out)

/-- A full Transformer Encoder Block (composed of Attn + MLP blocks). -/
noncomputable def transformer_encoder_block (S D D_ff : ℕ) :
    Chain (W (Fin S × Fin D)) (W (Fin S × Fin D)) :=
  let attn := transformer_attn_block S D
  let mlp := transformer_mlp_block S D D_ff
  Chain.append (Chain.single attn) mlp

end LeanSharp
