/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Core.Stats
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Theory.Alignment
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Basic

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
noncomputable def layernormForward (w : W (NormParam ι)) (x : W ι) (ε : ℝ) : W ι :=
  let x_norm := vectorNormalize x ε
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    let γ_i := (WithLp.equiv 2 _ w) (Sum.inl i)
    let β_i := (WithLp.equiv 2 _ w) (Sum.inr i)
    γ_i * (WithLp.equiv 2 _ x_norm) i + β_i

/-- Layer Normalization backward pass. -/
noncomputable def layernormBackward (w : W (NormParam ι)) (x : W ι) (g_out : W ι) (ε : ℝ) :
    W (NormParam ι) × W ι :=
  let μ := vectorMean x
  let σ_stable := Real.sqrt (vectorVariance x + ε)
  let g_w := WithLp.equiv 2 _ |>.symm fun
    | Sum.inl i => (WithLp.equiv 2 _ g_out) i * (((WithLp.equiv 2 _ x) i - μ) / σ_stable)
    | Sum.inr i => (WithLp.equiv 2 _ g_out) i
  -- Simplified gradient w.r.t input for the formal structure
  let g_x := WithLp.equiv 2 _ |>.symm fun i =>
    (WithLp.equiv 2 _ w) (Sum.inl i) * (WithLp.equiv 2 _ g_out) i / σ_stable
  (g_w, g_x)

/-- Layer Normalization Layer instance. -/
noncomputable def layerNorm (ι : Type) [Fintype ι] (ε : ℝ) : Layer (W ι) (W ι) where
  ParamDim := NormParam ι
  fintypeParamDim := inferInstance
  forward w x := layernormForward w x ε
  backward w x g := layernormBackward w x g ε

/-- **Mean Normalization**: For any input `x`, the vector mean of the normalized output
(with γ=1, β=0) is zero. -/
theorem layernorm_mean_zero [Nonempty ι] (x : W ι) (ε : ℝ) :
    let w_id : W (NormParam ι) :=
      WithLp.equiv 2 _ |>.symm fun | Sum.inl _ => 1 | Sum.inr _ => 0
    vectorMean (layernormForward w_id x ε) = 0 := by
  unfold layernormForward
  simp only [Equiv.apply_symm_apply, one_mul, add_zero]
  exact vectorMean_normalize x ε

/-- **LayerNorm Smoothness**: Layer Normalization is $C^2$ provided ε > 0. -/
theorem contDiff_layernormForward (w : W (NormParam ι)) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (fun x => layernormForward w x ε) := by
  unfold layernormForward
  apply contDiff_piLp'
  intro i
  apply ContDiff.add
  · apply ContDiff.mul
    · exact contDiff_const
    · have h1 : ContDiff ℝ 2 (fun x : W ι => vectorNormalize x ε) :=
        contDiff_vectorNormalize ι hε |>.of_le le_top
      have h2 : ContDiff ℝ 2 (fun (x : W ι) => (WithLp.equiv 2 (ι → ℝ) x) i) :=
        contDiff_piLp_apply (p := 2) (i := i) |>.of_le le_top
      exact ContDiff.comp h2 h1
  · exact contDiff_const

/-- **LayerNorm Forward Lipschitz**: The LayerNorm forward pass is locally Lipschitz
    on `Metric.ball 0 R` for any R > 0, provided ε > 0. -/
theorem layernorm_forward_lipschitz (w : W (NormParam ι)) (ε : ℝ) (hε : 0 < ε) (R : ℝ)
    (hR : 0 < R) :
    ∃ K, LipschitzOnWith K (fun x => layernormForward w x ε) (Metric.ball 0 R) :=
  lipschitzOnWith_closedBall_of_contDiff_two (fun x => layernormForward w x ε) R hR
    (contDiff_layernormForward w hε)

/-- **LayerNorm Stability Certificate**: Bundles the LayerNorm layer's forward pass
    with its Lipschitz constant and $C^2$ smoothness proof. -/
noncomputable def layerNormCertificate (w : W (NormParam ι)) (ε : ℝ) (hε : 0 < ε) (R : ℝ)
    (hR : 0 < R) :
    StabilityCertificate (W ι) (W ι) where
  f := fun x => layernormForward w x ε
  S := Metric.ball 0 R
  K := (layernorm_forward_lipschitz w ε hε R hR).choose
  h_lipschitz := (layernorm_forward_lipschitz w ε hε R hR).choose_spec
  h_smooth := (contDiff_layernormForward w hε).contDiffOn

end LeanSharp
