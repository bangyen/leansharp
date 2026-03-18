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

## Definitions

* `patchEmbedding`.
* `vitArchitecture`.
-/

/-- Patch Embedding Layer: Maps an image (C x H x W) to a sequence (S x D). -/
noncomputable def patchEmbedding (nc nh nw np ns nd : ℕ)
    [NeZero nh] [NeZero nw] [NeZero np] [NeZero ns] :
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
  backward w x g_out :=
    let w_vec := WithLp.equiv 2 _ w
    let x_vec := WithLp.equiv 2 _ x
    let g_out_f := WithLp.equiv 2 _ g_out
    -- Gradient w.r.t weights w
    let g_w := WithLp.equiv 2 _ |>.symm fun ((c, ph, pw), d) =>
      ∑ s : Fin ns,
        let row : ℕ := (s : ℕ) / (nw / np) * np + (ph : ℕ)
        let col : ℕ := (s : ℕ) % (nw / np) * np + (pw : ℕ)
        g_out_f (s, d) * x_vec (c, Fin.ofNat nh row, Fin.ofNat nw col)
    -- Gradient w.r.t input x
    let g_x := WithLp.equiv 2 _ |>.symm fun (c, h, w) =>
      let s_idx : ℕ := (h : ℕ) / np * (nw / np) + (w : ℕ) / np
      let ph : ℕ := (h : ℕ) % np
      let pw : ℕ := (w : ℕ) % np
      ∑ d : Fin nd, g_out_f (Fin.ofNat ns s_idx, d) * w_vec
        ((c, Fin.ofNat np ph, Fin.ofNat np pw), d)
    (g_w, g_x)

/-- Full Vision Transformer (ViT) architecture. -/
noncomputable def vitArchitecture (nc nh nw np ns nd nd_ff : ℕ)
    [NeZero nh] [NeZero nw] [NeZero np] [NeZero ns] :
    Chain (LeanSharp.W (Fin nc × Fin nh × Fin nw)) (LeanSharp.W (Fin ns × Fin nd)) :=
  let patch := patchEmbedding nc nh nw np ns nd
  let transformer := transformerEncoderBlock ns nd nd_ff
  Chain.concat (Chain.single patch) transformer

end LeanSharp
