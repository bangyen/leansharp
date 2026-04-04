/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Core.Stats
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Theory.Alignment
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Normalization Layers

This module formalizes normalization layers, specifically Layer Normalization.

## Main definitions

* `layerNorm`: The Layer Normalization operation.
* `NormParam`: Parameter index type for scale (gamma) and shift (beta).

## Main theorems

* `layernorm_mean_zero`: Proves that LayerNorm output has mean zero.
-/

namespace LeanSharp

variable {ι : Type} [Fintype ι]

/-- The parameter index type for normalization: scale (gamma) and shift (beta). -/
abbrev NormParam (ι : Type) := ι ⊕ ι

/-- Layer Normalization forward pass: y = γ * (x - μ) / Real.sqrt(σ² + ε) + β. -/
noncomputable def layernormForward (w : W (NormParam ι)) (x : W ι) : W ι :=
  let x_norm := vectorNormalize x 0.00001
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    let γ_i := (WithLp.equiv 2 _ w) (Sum.inl i)
    let β_i := (WithLp.equiv 2 _ w) (Sum.inr i)
    γ_i * (WithLp.equiv 2 _ x_norm) i + β_i

/-- Layer Normalization backward pass. -/
noncomputable def layernormBackward (w : W (NormParam ι)) (x : W ι) (g_out : W ι) :
    W (NormParam ι) × W ι :=
  let μ := vectorMean x
  let σ_stable := Real.sqrt (vectorVariance x + 0.00001)
  let g_w := WithLp.equiv 2 _ |>.symm fun
    | Sum.inl i => (WithLp.equiv 2 _ g_out) i * (((WithLp.equiv 2 _ x) i - μ) / σ_stable)
    | Sum.inr i => (WithLp.equiv 2 _ g_out) i
  -- Simplified gradient w.r.t input for the formal structure
  let g_x := WithLp.equiv 2 _ |>.symm fun i =>
    (WithLp.equiv 2 _ w) (Sum.inl i) * (WithLp.equiv 2 _ g_out) i / σ_stable
  (g_w, g_x)

/-- Layer Normalization Layer instance. -/
noncomputable def layerNorm (ι : Type) [Fintype ι] : Layer (W ι) (W ι) where
  ParamDim := NormParam ι
  fintypeParamDim := inferInstance
  forward := layernormForward
  backward := layernormBackward

/-- **Mean Normalization**: For any input `x`, the vector mean of the normalized output
(with γ=1, β=0) is zero. -/
theorem layernorm_mean_zero [Nonempty ι] (x : W ι) :
    let w_id : W (NormParam ι) :=
      WithLp.equiv 2 _ |>.symm fun | Sum.inl _ => 1 | Sum.inr _ => 0
    vectorMean (layernormForward w_id x) = 0 := by
  unfold layernormForward
  simp only [Equiv.apply_symm_apply, one_mul, add_zero]
  exact vectorMean_normalize x 0.00001

/-- **LayerNorm Smoothness**: Layer Normalization is $C^2$. -/
theorem contDiff_layernormForward [Nonempty ι] (w : W (NormParam ι)) :
    ContDiff ℝ 2 (layernormForward w) := by
  unfold layernormForward
  apply contDiff_piLp'
  intro i
  apply ContDiff.add
  · apply ContDiff.mul
    · exact contDiff_const
    · have h1 : ContDiff ℝ 2 (fun x : W ι => vectorNormalize x 0.00001) :=
        contDiff_vectorNormalize ι (by norm_num) |>.of_le le_top
      have h2 : ContDiff ℝ 2 (fun (x : W ι) => (WithLp.equiv 2 (ι → ℝ) x) i) :=
        contDiff_piLp_apply (p := 2) (i := i) |>.of_le le_top
      exact ContDiff.comp h2 h1
  · exact contDiff_const

/-- **LayerNorm Forward Lipschitz**: The LayerNorm forward pass is locally Lipschitz
    on `Metric.ball 0 1000`.

    **Proof**: `layernormForward w` is globally $C^2$ (proven above via
    `contDiff_layernormForward`). By differentiability, the Fréchet derivative is
    continuous. The Extreme Value Theorem on the compact `closedBall 0 1000` yields
    a maximum derivative norm `K`, and the Mean Value Theorem for convex sets
    gives `LipschitzOnWith K` on the ball. -/
theorem layernorm_forward_lipschitz [Nonempty ι] (w : W (NormParam ι)) :
    ∃ K, LipschitzOnWith K (layernormForward w) (Metric.ball 0 1000) := by
  let f := layernormForward w
  have h_c2 : ContDiff ℝ 2 f := contDiff_layernormForward w
  have h_diff : ∀ x, DifferentiableAt ℝ f x := fun x => h_c2.differentiable (by decide) x
  have h_cont_deriv : Continuous (fderiv ℝ f) := h_c2.continuous_fderiv (by decide)
  have h_compact : IsCompact (Metric.closedBall (0 : W ι) 1000) :=
    isCompact_closedBall (0 : W ι) 1000
  have h_cont_norm : Continuous (fun x => ‖fderiv ℝ f x‖) :=
    continuous_norm.comp h_cont_deriv
  have h_nonempty : (Metric.closedBall (0 : W ι) 1000).Nonempty :=
    Metric.nonempty_closedBall.mpr (by norm_num)
  obtain ⟨x0, _, h_max⟩ := IsCompact.exists_isMaxOn h_compact h_nonempty h_cont_norm.continuousOn
  let K := ‖fderiv ℝ f x0‖₊
  use K
  have h_lips : LipschitzOnWith K f (Metric.closedBall 0 1000) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact fun x _ => h_diff x
    · exact fun x hx => h_max hx
    · exact convex_closedBall 0 1000
  exact h_lips.mono Metric.ball_subset_closedBall

/-- **LayerNorm Stability Certificate**: Bundles the LayerNorm layer's forward pass
    with its Lipschitz constant and $C^2$ smoothness proof. -/
noncomputable def layerNormCertificate [Nonempty ι] (w : W (NormParam ι)) :
    StabilityCertificate (W ι) (W ι) where
  f := layernormForward w
  S := Metric.ball 0 1000
  K := (layernorm_forward_lipschitz w).choose
  h_lipschitz := (layernorm_forward_lipschitz w).choose_spec
  h_smooth := (contDiff_layernormForward w).contDiffOn

end LeanSharp
