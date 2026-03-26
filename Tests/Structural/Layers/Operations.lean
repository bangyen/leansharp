/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Layers.Basic.Activation
import LeanSharp.Layers.Basic.Residual
import LeanSharp.Layers.Normalization.LayerNorm

/-!
# Operations Tests

This module verifies normalization and residual connection layers.

## Examples
-/

namespace LeanSharp.Tests

/-- Test: LayerNorm Parameter Dimensions. -/
example (ι : Type) [Fintype ι] : (layerNorm ι).ParamDim = NormParam ι :=
  rfl

/-- Test: Residual Layer Dimensions. -/
example {ι : Type} [Fintype ι] (L : Layer (W ι) (W ι)) :
    (residualLayer L).ParamDim = L.ParamDim :=
  rfl

/-- Test: LayerNorm output has zero mean. -/
example {ι : Type} [Fintype ι] [Nonempty ι] (x : W ι) :
    vectorMean ((layerNorm ι).forward (WithLp.equiv 2 _ |>.symm fun
      | Sum.inl _ => 1
      | Sum.inr _ => 0) x) = 0 :=
  layernorm_mean_zero x

/-- Test: LayerNorm Parameter non-emptiness. -/
example (ι : Type) [Fintype ι] [Nonempty ι] :
  Nonempty (NormParam ι) := by
  unfold NormParam
  infer_instance

/-- Test: Residual identity: x + relu(x) where x > 0. -/
example : (residualLayer (reluLayer (Fin 1))).forward 0
    (WithLp.equiv 2 _ |>.symm fun _ => (1 : ℝ)) =
    (WithLp.equiv 2 _ |>.symm fun _ => (2 : ℝ)) := by
  unfold residualLayer reluLayer
  dsimp only [WithLp.equiv_apply, WithLp.equiv_symm_apply, relu]
  ext i
  norm_num

end LeanSharp.Tests
