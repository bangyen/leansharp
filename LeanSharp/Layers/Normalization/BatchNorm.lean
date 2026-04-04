/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Core.Stats
import LeanSharp.Layers.Normalization.LayerNorm
import LeanSharp.Theory.Alignment
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

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
    (w : W (NormParam (Fin D))) (x : W (Fin N × Fin D)) :
    W (Fin N × Fin D) :=
  WithLp.equiv 2 _ |>.symm fun (n, d) =>
    let x_d := batchSlice x d
    let x_norm := vectorNormalize x_d 0.00001
    let γ_d := (WithLp.equiv 2 _ w) (Sum.inl d)
    let β_d := (WithLp.equiv 2 _ w) (Sum.inr d)
    γ_d * (WithLp.equiv 2 _ x_norm) n + β_d

/-- Batch Normalization backward pass. -/
noncomputable def batchnormBackward {N D : ℕ}
    (w : W (NormParam (Fin D))) (x : W (Fin N × Fin D))
    (g_out : W (Fin N × Fin D)) : W (NormParam (Fin D)) × W (Fin N × Fin D) :=
  let μ (d : Fin D) := batchMean x d
  let σ_stable (d : Fin D) := Real.sqrt (batchVar x d + 0.00001)
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
noncomputable def batchNormLayer (N D : ℕ) :
    Layer (W (Fin N × Fin D)) (W (Fin N × Fin D)) where
  ParamDim := NormParam (Fin D)
  fintypeParamDim := inferInstance
  forward := batchnormForward
  backward := batchnormBackward

/-- **Mean Normalization**: For any input `x`, the batch mean of the normalized output
(with γ=1, β=0) is zero for all feature dimensions `d`. -/
theorem batchnorm_mean_zero {N D : ℕ} (hN : 0 < N) (x : W (Fin N × Fin D)) (d : Fin D) :
    let w_id : W (NormParam (Fin D)) :=
      WithLp.equiv 2 _ |>.symm fun | Sum.inl _ => 1 | Sum.inr _ => 0
    batchMean (batchnormForward w_id x) d = 0 := by
  unfold batchMean batchnormForward batchSlice
  simp only [Equiv.apply_symm_apply, one_mul, add_zero]
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact vectorMean_normalize (batchSlice x d) 0.00001

/-- **BatchNorm Smoothness**: Batch Normalization is $C^\infty$ (and thus $C^2$) because
    `vectorNormalize` avoids division by zero via `ε > 0`. -/
theorem contDiff_batchnormForward {N D : ℕ} (w : W (NormParam (Fin D))) :
    ContDiff ℝ 2 (fun x => batchnormForward w x (N := N)) := by
  unfold batchnormForward
  apply contDiff_piLp'
  intro p
  let n := p.1
  let d := p.2
  apply ContDiff.add
  · apply ContDiff.mul
    · exact contDiff_const
    · have h1 : ContDiff ℝ 2
          (fun x : W (Fin N × Fin D) => vectorNormalize (batchSlice x d) 0.00001) := by
        have hA : ContDiff ℝ 2 (fun x : W (Fin N × Fin D) => batchSlice x d) := by
          unfold batchSlice
          apply contDiff_piLp'
          intro i
          exact contDiff_piLp_apply (p := 2) (i := (i, d)) |>.of_le le_top
        have hB : ContDiff ℝ 2 (fun x : W (Fin N) => vectorNormalize x 0.00001) :=
          contDiff_vectorNormalize (Fin N) (by norm_num) |>.of_le le_top
        exact hB.comp hA
      have h2 : ContDiff ℝ 2 (fun (x : W (Fin N)) => (WithLp.equiv 2 _ x) n) :=
        contDiff_piLp_apply (p := 2) (i := n) |>.of_le le_top
      exact h2.comp h1
  · exact contDiff_const

/-- **BatchNorm Forward Lipschitz**: The output of BatchNorm is locally Lipschitz continuous
    on `Metric.ball 0 1000`.

    **Proof**: `batchnormForward w` is globally $C^2$ (proven by
    `contDiff_batchnormForward`). The Extreme Value Theorem on `closedBall 0 1000` yields
    a maximum Fréchet derivative norm `K`, and the Mean Value Theorem gives
    `LipschitzOnWith K` on the ball. -/
theorem batchnorm_forward_lipschitz {N D : ℕ} (w : W (NormParam (Fin D))) :
    ∃ K, LipschitzOnWith K (fun x => batchnormForward w x (N := N)) (Metric.ball 0 1000) := by
  let f := fun x => batchnormForward w x (N := N)
  have h_c2 : ContDiff ℝ 2 f := contDiff_batchnormForward w
  have h_diff : ∀ x, DifferentiableAt ℝ f x := fun x => h_c2.differentiable (by decide) x
  have h_cont_deriv : Continuous (fderiv ℝ f) := h_c2.continuous_fderiv (by decide)
  have h_compact : IsCompact (Metric.closedBall (0 : W (Fin N × Fin D)) 1000) :=
    isCompact_closedBall (0 : W (Fin N × Fin D)) 1000
  have h_cont_norm : Continuous (fun x => ‖fderiv ℝ f x‖) :=
    continuous_norm.comp h_cont_deriv
  have h_nonempty : (Metric.closedBall (0 : W (Fin N × Fin D)) 1000).Nonempty :=
    Metric.nonempty_closedBall.mpr (by norm_num)
  obtain ⟨x0, _, h_max⟩ :=
    IsCompact.exists_isMaxOn h_compact h_nonempty h_cont_norm.continuousOn
  let K := ‖fderiv ℝ f x0‖₊
  use K
  have h_lips : LipschitzOnWith K f (Metric.closedBall 0 1000) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact fun x _ => h_diff x
    · exact fun x hx => h_max hx
    · exact convex_closedBall 0 1000
  exact h_lips.mono Metric.ball_subset_closedBall

/-- **BatchNorm Stability Certificate**: Bundles the BatchNorm layer's forward pass
    with its Lipschitz constant and $C^2$ smoothness proof. -/
noncomputable def batchNormCertificate (N D : ℕ) (w : W (NormParam (Fin D))) :
    StabilityCertificate (W (Fin N × Fin D)) (W (Fin N × Fin D)) where
  f := batchnormForward w
  S := Metric.ball 0 1000
  K := (batchnorm_forward_lipschitz w).choose
  h_lipschitz := (batchnorm_forward_lipschitz w).choose_spec
  h_smooth := (contDiff_batchnormForward w).contDiffOn

end LeanSharp
