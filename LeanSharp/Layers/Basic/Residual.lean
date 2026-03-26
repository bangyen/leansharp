/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace LeanSharp

/-!
# Residual Layers

This module formalizes residual skip-connections $y = x + f(x)$.
Residual blocks are essential for training deep architectures by mitigating
gradient vanishing.

## Main definitions

* `residualLayer`: A wrapper that adds a skip connection to an existing layer.
* `residual_lipschitz`: Inherited Lipschitz continuity for residual blocks.
* `residual_contDiff`: Inherited smoothness for residual blocks.

## Theorems

* `residual_lipschitz`.
* `residual_contDiff`.
-/

/-- A Residual Block is a wrapper that adds a skip connection: $y = x + f(x)$.
    The input and output spaces must be the same Euclidean space. -/
noncomputable def Layer.residualLayer {ι : Type} [Fintype ι] (f : Layer (W ι) (W ι)) :
    Layer (W ι) (W ι) :=
  { ParamDim := f.ParamDim
    fintypeParamDim := f.fintypeParamDim
    forward := fun w x => x + f.forward w x
    backward := fun w x g_out =>
      let (g_w, g_x_inner) := f.backward w x g_out
      (g_w, g_out + g_x_inner) }

/-- **Residual Lipschitz**: If the inner layer `f` is $K$-Lipschitz, then the
    residual layer $x + f(x)$ is $(1 + K)$-Lipschitz. -/
theorem Layer.residual_lipschitz {ι : Type} [Fintype ι] (f : Layer (W ι) (W ι))
    (w : W f.ParamDim) (K : NNReal) (hL : LipschitzWith K (f.forward w)) :
    LipschitzWith (1 + K) ((Layer.residualLayer f).forward w) := by
  -- y(x) = id(x) + f(x)
  have h_id : LipschitzWith 1 (fun x : W ι => x) := LipschitzWith.id
  exact h_id.add hL

/-- **Residual Smoothness**: If the inner layer `f` is $C^k$, then the
    residual layer is also $C^k$. -/
theorem Layer.residual_contDiff {ι : Type} [Fintype ι] (f : Layer (W ι) (W ι))
    (w : W f.ParamDim) (k : ℕ) (hC : ContDiff ℝ k (f.forward w)) :
    ContDiff ℝ k ((Layer.residualLayer f).forward w) := by
  apply ContDiff.add
  · exact contDiff_id
  · exact hC

end LeanSharp
