/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Core.Stats
import LeanSharp.Layers.Normalization.LayerNorm
import LeanSharp.Theory.Alignment
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Basic

namespace LeanSharp

/-!
# Batch Normalization

This module formalizes Batch Normalization for 2D inputs (Batch × Features).
Normalization is performed across the batch dimension.

## Main definitions

* `batchNormLayer`: The Batch Normalization operation.
-/

/-- Extracts a slice of the batch for a specific feature dimension `d`. -/
noncomputable def batchSlice {N D : ℕ} (x : W (Fin N × Fin D)) (d : Fin D) : W (Fin N) :=
  WithLp.equiv 2 _ |>.symm fun n => (WithLp.equiv 2 _ x) (n, d)

/-- Batch mean for a specific feature dimension `d`. -/
noncomputable def batchMean {N D : ℕ} (x : W (Fin N × Fin D)) (d : Fin D) : ℝ :=
  vectorMean (batchSlice x d)

/-- Batch variance for a specific feature dimension `d`. -/
noncomputable def batchVar {N D : ℕ} (x : W (Fin N × Fin D)) (d : Fin D) : ℝ :=
  vectorVariance (batchSlice x d)

/-- Batch Normalization forward pass. -/
noncomputable def batchnormForward {N D : ℕ}
    (w : W (NormParam (Fin D))) (x : W (Fin N × Fin D)) (ε : ℝ) :
    W (Fin N × Fin D) :=
  WithLp.equiv 2 _ |>.symm fun (n, d) =>
    let x_d := batchSlice x d
    let x_norm := vectorNormalize x_d ε
    let γ_d := (WithLp.equiv 2 _ w) (Sum.inl d)
    let β_d := (WithLp.equiv 2 _ w) (Sum.inr d)
    γ_d * (WithLp.equiv 2 _ x_norm) n + β_d

/-- Batch Normalization backward pass. -/
noncomputable def batchnormBackward {N D : ℕ}
    (w : W (NormParam (Fin D))) (x : W (Fin N × Fin D))
    (g_out : W (Fin N × Fin D)) (ε : ℝ) : W (NormParam (Fin D)) × W (Fin N × Fin D) :=
  let μ (d : Fin D) := batchMean x d
  let σ_stable (d : Fin D) := Real.sqrt (batchVar x d + ε)
  let g_w := WithLp.equiv 2 _ |>.symm fun
    | Sum.inl d => ∑ n : Fin N, (WithLp.equiv 2 _ g_out) (n, d) *
        (((WithLp.equiv 2 _ x) (n, d) - μ d) / σ_stable d)
    | Sum.inr d => ∑ n : Fin N, (WithLp.equiv 2 _ g_out) (n, d)
  -- Simplified gradient w.r.t input for structural purposes
  let g_x := WithLp.equiv 2 _ |>.symm fun p =>
    let (_, d) := p
    ((WithLp.equiv 2 _ w) (Sum.inl d) * (WithLp.equiv 2 _ g_out) p) / σ_stable d
  (g_w, g_x)

/-- Batch Normalization Layer instance. -/
noncomputable def batchNormLayer (N D : ℕ) (ε : ℝ) :
    Layer (W (Fin N × Fin D)) (W (Fin N × Fin D)) where
  ParamDim := NormParam (Fin D)
  fintypeParamDim := inferInstance
  forward w x := batchnormForward w x ε
  backward w x g := batchnormBackward w x g ε

end LeanSharp
