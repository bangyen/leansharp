/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Layers.Basic.Dropout
import LeanSharp.Layers.Specialized.Quantization
import LeanSharp.Layers.Architectures.Transformer
import LeanSharp.Layers.Architectures.ViT
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

/-- Test: Dropout zeroes everything when mask is 0. -/
theorem test_dropout_zero {ι : Type} (p : ℝ) (x : W ι) :
    dropout_forward p 0 x = 0 := by
  unfold dropout_forward
  simp only
  ext i
  simp

end LeanSharp.Tests
