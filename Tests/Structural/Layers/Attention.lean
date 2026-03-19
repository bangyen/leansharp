/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Layers.Architectures.Attention
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Attention Tests

This module verifies forward and backward pass identities for Multi-Head
Attention (MHA) layers.

## Examples
-/

namespace LeanSharp.Tests

/-- Test: MHA output is zero when all projections are zero. -/
example {S D : ℕ} (x : W (Fin S × Fin D)) :
    (mhaLayer S D).forward 0 x = 0 := by
  unfold mhaLayer
  dsimp only [
    WithLp.equiv_apply,
    WithLp.equiv_symm_apply,
    PiLp.zero_apply
  ]
  unfold attentionForward
  ext p
  simp only [
    mul_zero,
    Finset.sum_const_zero,
    WithLp.equiv_apply,
    zero_div,
    WithLp.equiv_symm_apply,
    PiLp.zero_apply
  ]

/-- Test: MHA Parameter Dimensions. -/
example (S D : ℕ) [NeZero S] [NeZero D] :
    (mhaLayer S D).ParamDim = ATTParam (Fin D) :=
  rfl

/-- Test: Attention Block existence verification. -/
example (S D : ℕ) [NeZero S] [NeZero D] :
    Nonempty (mhaLayer S D).ParamDim := by
  exact ⟨Sum.inl (0, 0)⟩

/-- Test: Attention Head Indexing. -/
example (D : ℕ) :
    ATTParam (Fin D) =
      ((Fin D × Fin D) ⊕ (Fin D × Fin D) ⊕ (Fin D × Fin D) ⊕ (Fin D × Fin D)) :=
  rfl

end LeanSharp.Tests
