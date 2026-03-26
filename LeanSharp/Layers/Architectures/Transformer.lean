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

/-- Feature-wise Layer Normalization. Applies `layerNorm` independently to each sequence element. -/
noncomputable def featureNormLayer (S D : ℕ) : Layer (W (Fin S × Fin D)) (W (Fin S × Fin D)) :=
  broadcastLayer (Fin S) (layerNorm (Fin D))

/-- The Attention Block: Residual(LN + MHA) -/
noncomputable def transformerAttnBlock (S D : ℕ) :
    Layer (W (Fin S × Fin D)) (W (Fin S × Fin D)) :=
  let ln := featureNormLayer S D
  let attn := mhaLayer S D
  (Chain.append (Chain.single ln) attn).toLayer.residualLayer

/-- The MLP Block: Residual(LN + Linear + ReLU + Linear) -/
noncomputable def transformerMlpBlock (S D D_ff : ℕ) :
    Layer (W (Fin S × Fin D)) (W (Fin S × Fin D)) :=
  let ln := featureNormLayer S D
  let l1 := broadcastLayer (Fin S) (linearLayer (Fin D) (Fin D_ff))
  let relu := smoothReluLayer (Fin S × Fin D_ff)
  let l2 := broadcastLayer (Fin S) (linearLayer (Fin D_ff) (Fin D))
  let mlp := Chain.append (Chain.append (Chain.append (Chain.single ln) l1) relu) l2
  mlp.toLayer.residualLayer

/-- A full Transformer Encoder Block (composed of Attn + MLP blocks). -/
noncomputable def transformerEncoderBlock (S D D_ff : ℕ) :
    Chain (W (Fin S × Fin D)) (W (Fin S × Fin D)) :=
  Chain.append (Chain.single (transformerAttnBlock S D)) (transformerMlpBlock S D D_ff)

end LeanSharp
