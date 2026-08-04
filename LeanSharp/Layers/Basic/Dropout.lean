/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace LeanSharp

/-!
# Dropout Layer

This module formalizes a Dropout layer.
For structural verification in our deterministic framework, we model dropout
as a layer where the "mask" is provided externally or treated as part of the
non-learnable execution state.

> [!IMPORTANT]
> **The Fixed-Mask Paradox**: The mask is treated as a fixed parameter for the
> duration of the forward/backward pass. In a real stochastic training loop, the
> mask changes every step, so the "composed" process across steps is non-differentiable.
> We "buy" formal stability guarantees for the optimizer by projecting the
> stochastic layer into a family of deterministic linear operators.

## Main definitions

* `dropoutForward`: The dropout forward pass, $y = x \odot \mathrm{mask} / (1 - p)$.
-/

variable {ι : Type*} [Fintype ι]

/-- Dropout forward pass: y = x ⊙ mask / (1 - p).
    For formal consistency, we take the mask as an input vector. -/
noncomputable def dropoutForward (p : ℝ) (mask : W ι) (x : W ι) : W ι :=
  let scale := 1 / (1 - p)
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    (WithLp.equiv 2 _ x) i * (WithLp.equiv 2 _ mask) i * scale

end LeanSharp
