/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Layers.Architectures.Transformer
import LeanSharp.Layers.Architectures.VisionTransformer

/-!
# Architecture Tests

This module verifies architectural invariants for complex models like
Transformers and Vision Transformers (ViT).

## Examples
-/

namespace LeanSharp.Tests

/-- Test: Transformer Encoder Block structure verifies as a chain of length 2. -/
example (S D D_ff : ℕ) [NeZero S] [NeZero D] :
    (transformerEncoderBlock S D D_ff).length = 2 :=
  rfl

/-- Test: ViT Patch Embedding Parameter Dimensions. -/
example (nc nh nw np ns nd : ℕ) [NeZero nh] [NeZero nw] [NeZero np] [NeZero ns] :
    (patchEmbedding nc nh nw np ns nd).ParamDim =
      ((Fin nc × Fin np × Fin np) × Fin nd) :=
  rfl

/-- Test: Full ViT Architecture Chain Length (Patch + Attn + MLP). -/
example (nc nh nw np ns nd nd_ff : ℕ) [NeZero nh] [NeZero nw] [NeZero np] [NeZero ns] :
    (vitArchitecture nc nh nw np ns nd nd_ff).length = 3 := by
  unfold vitArchitecture transformerEncoderBlock
  simp only [Chain.concat, Chain.length]

/-- Test: Transformer Encoder Block input/output types. -/
example (S D D_ff : ℕ) [NeZero S] [NeZero D] :
    Nonempty (Chain (W (Fin S × Fin D)) (W (Fin S × Fin D))) := by
  exact ⟨transformerEncoderBlock S D D_ff⟩

end LeanSharp.Tests
