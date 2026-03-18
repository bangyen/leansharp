/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models

namespace LeanSharp

/-!
# Dropout Layer

This module formalizes a Dropout layer.
For structural verification in our deterministic framework, we model dropout
as a layer where the "mask" is provided externally or treated as part of the
non-learnable execution state.

## Main definitions

* `dropoutLayer`: Regularization by zeroing out elements.
-/

variable {ι : Type*} [Fintype ι]

/-- Dropout forward pass: y = x ⊙ mask / (1 - p).
    For formal consistency, we take the mask as an input vector. -/
noncomputable def dropoutForward (p : ℝ) (mask : W ι) (x : W ι) : W ι :=
  let scale := 1 / (1 - p)
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    (WithLp.equiv 2 _ x) i * (WithLp.equiv 2 _ mask) i * scale

/-- Dropout backward pass. -/
noncomputable def dropoutBackward (p : ℝ) (mask : W ι) (g_out : W ι) : W ι :=
  let scale := 1 / (1 - p)
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    (WithLp.equiv 2 _ g_out) i * (WithLp.equiv 2 _ mask) i * scale

/-- Dropout Layer instance.
    The "parameters" here represent the dropout mask (which would be
    sampled stochastically in a runtime setting). -/
noncomputable def dropoutLayer (ι : Type) [Fintype ι] (p : ℝ) :
    Layer (W ι) (W ι) where
  ParamDim := ι
  fintypeParamDim := inferInstance
  forward mask x := dropoutForward p mask x
  backward mask x g_out :=
    let _ := x;
    (0, dropoutBackward p mask g_out)

end LeanSharp
