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

## Main theorems

* `batchnorm_mean_zero`: Proves that BatchNorm output has mean zero.
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

/-- **Mean Normalization**: For any input `x`, the batch mean of the normalized output
(with γ=1, β=0) is zero for all feature dimensions `d`. -/
theorem batchnorm_mean_zero {N D : ℕ} (hN : 0 < N) (x : W (Fin N × Fin D)) (d : Fin D) (ε : ℝ) :
    let w_id : W (NormParam (Fin D)) :=
      WithLp.equiv 2 _ |>.symm fun | Sum.inl _ => 1 | Sum.inr _ => 0
    batchMean (batchnormForward w_id x ε) d = 0 := by
  unfold batchMean batchnormForward batchSlice
  simp only [Equiv.apply_symm_apply, one_mul, add_zero]
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact vectorMean_normalize (batchSlice x d) ε

/-- **BatchNorm Smoothness**: Batch Normalization is $C^2$ provided ε > 0. -/
theorem contDiff_batchnormForward {N D : ℕ} (w : W (NormParam (Fin D))) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (fun x => batchnormForward w x (N := N) ε) := by
  unfold batchnormForward
  apply contDiff_piLp'
  intro p
  let n := p.1
  let d := p.2
  apply ContDiff.add
  · apply ContDiff.mul
    · exact contDiff_const
    · have h1 : ContDiff ℝ 2
          (fun x : W (Fin N × Fin D) => vectorNormalize (batchSlice x d) ε) := by
        have hA : ContDiff ℝ 2 (fun x : W (Fin N × Fin D) => batchSlice x d) := by
          unfold batchSlice
          apply contDiff_piLp'
          intro i
          exact contDiff_piLp_apply (p := 2) (i := (i, d)) |>.of_le le_top
        have hB : ContDiff ℝ 2 (fun x : W (Fin N) => vectorNormalize x ε) :=
          contDiff_vectorNormalize (Fin N) hε |>.of_le le_top
        exact hB.comp hA
      have h2 : ContDiff ℝ 2 (fun (x : W (Fin N)) => (WithLp.equiv 2 _ x) n) :=
        contDiff_piLp_apply (p := 2) (i := n) |>.of_le le_top
      exact h2.comp h1
  · exact contDiff_const

/-- **BatchNorm Forward Lipschitz**: The output of BatchNorm is locally Lipschitz continuous
    on `Metric.ball 0 R` for any R > 0, provided ε > 0. -/
theorem batchnorm_forward_lipschitz {N D : ℕ} (w : W (NormParam (Fin D))) (ε : ℝ) (hε : 0 < ε)
    (R : ℝ) (hR : 0 < R) :
    ∃ K, LipschitzOnWith K (fun x => batchnormForward w x (N := N) ε) (Metric.ball 0 R) :=
  lipschitzOnWith_closedBall_of_contDiff_two (fun x => batchnormForward w x (N := N) ε) R hR
    (contDiff_batchnormForward w hε)

/-- **BatchNorm Stability Certificate**: Bundles the BatchNorm layer's forward pass
    with its Lipschitz constant and $C^2$ smoothness proof. -/
noncomputable def batchNormCertificate (N D : ℕ) (w : W (NormParam (Fin D))) (ε : ℝ) (hε : 0 < ε)
    (R : ℝ) (hR : 0 < R) :
    StabilityCertificate (W (Fin N × Fin D)) (W (Fin N × Fin D)) where
  f := fun x => batchnormForward w x ε
  S := Metric.ball 0 R
  K := (batchnorm_forward_lipschitz w ε hε R hR).choose
  h_lipschitz := (batchnorm_forward_lipschitz w ε hε R hR).choose_spec
  h_smooth := (contDiff_batchnormForward w hε).contDiffOn

end LeanSharp
