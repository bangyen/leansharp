/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Layers.Architectures.Transformer
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LeanSharp

/-!
# Vision Transformer (ViT)

This module formalizes the Vision Transformer architecture.
It includes:
1. Patch Embedding: Projects image patches into a sequence of vectors.
2. ViT Encoder: A composition of Patch Embedding and Transformer Blocks.
-/

/-- Patch Embedding Layer: Maps an image (C x H x W) to a sequence (S x D). -/
noncomputable def patch_embedding (nc nh nw np ns nd : ℕ) [NeZero nh] [NeZero nw] :
    Layer (LeanSharp.W (Fin nc × Fin nh × Fin nw)) (LeanSharp.W (Fin ns × Fin nd)) where
  ParamDim := (Fin nc × Fin np × Fin np) × Fin nd
  fintypeParamDim := inferInstance
  forward w x :=
    let w_vec := WithLp.equiv 2 _ w
    let x_vec := WithLp.equiv 2 _ x
    WithLp.equiv 2 (Fin ns × Fin nd → ℝ) |>.symm fun (s, d) =>
      ∑ c : Fin nc, ∑ ph : Fin np, ∑ pw : Fin np,
        let row : ℕ := (s : ℕ) / (nw / np) * np + (ph : ℕ)
        let col : ℕ := (s : ℕ) % (nw / np) * np + (pw : ℕ)
        x_vec (c, Fin.ofNat nh row, Fin.ofNat nw col) * w_vec ((c, ph, pw), d)
  backward _ _ _ := (0, 0)

/-- Full Vision Transformer (ViT) architecture. -/
noncomputable def vit_architecture (nc nh nw np ns nd nd_ff : ℕ) [NeZero nh] [NeZero nw] :
    Chain (LeanSharp.W (Fin nc × Fin nh × Fin nw)) (LeanSharp.W (Fin ns × Fin nd)) :=
  let patch := patch_embedding nc nh nw np ns nd
  let transformer := transformer_encoder_block ns nd nd_ff
  Chain.concat (Chain.single patch) transformer

end LeanSharp
