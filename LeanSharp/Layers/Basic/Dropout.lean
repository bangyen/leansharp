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

## Main definitions

* `dropoutLayer`: Regularization by zeroing out elements.
* `dropout_lipschitz`: Lipschitz continuity of the dropout forward pass.
* `dropout_contDiff`: Smoothness of the dropout forward pass.

## Theorems

* `dropout_lipschitz`.
* `dropout_contDiff`.
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

/-- **Dropout Lipschitz**: The dropout layer's forward pass is Lipschitz continuous.
    The Lipschitz constant depends on the mask and the scale `1 / (1 - p)`. -/
theorem dropout_lipschitz (p : ℝ) (mask : W ι) :
    ∃ K : NNReal, LipschitzWith K (dropoutForward p mask (ι := ι)) := by
  let scale := 1 / (1 - p)
  let L : W ι →L[ℝ] W ι := (WithLp.linearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp <|
    (ContinuousLinearMap.pi fun i =>
      (ContinuousLinearMap.proj i).smulRight (scale * (WithLp.equiv 2 _ mask) i)).comp <|
    (WithLp.linearEquiv 2 ℝ _).toContinuousLinearMap
  use ‖L‖₊
  have h_linear (x : W ι) : dropoutForward p mask x = L x := by
    ext i
    unfold dropoutForward L
    simp only [
      WithLp.equiv_apply, one_div, WithLp.equiv_symm_apply, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe, WithLp.linearEquiv_apply,
      AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, WithLp.addEquiv_apply,
      ContinuousLinearMap.coe_pi', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, WithLp.linearEquiv_symm_apply,
      Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, WithLp.addEquiv_symm_apply
    ]
    ring
  rw [funext h_linear]
  exact L.lipschitz

/-- **Dropout Smoothness**: The dropout layer's forward pass is $C^\infty$
    (and thus $C^2$) because it is a linear operator. -/
theorem dropout_contDiff (p : ℝ) (mask : W ι) :
    ContDiff ℝ 2 (dropoutForward p mask (ι := ι)) := by
  let scale := 1 / (1 - p)
  let L : W ι →L[ℝ] W ι := (WithLp.linearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp <|
    (ContinuousLinearMap.pi fun i =>
      (ContinuousLinearMap.proj i).smulRight (scale * (WithLp.equiv 2 _ mask) i)).comp <|
    (WithLp.linearEquiv 2 ℝ _).toContinuousLinearMap
  have h_linear (x : W ι) : dropoutForward p mask x = L x := by
    ext i
    unfold dropoutForward L
    simp only [
      WithLp.equiv_apply, one_div, WithLp.equiv_symm_apply, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe, WithLp.linearEquiv_apply,
      AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, WithLp.addEquiv_apply,
      ContinuousLinearMap.coe_pi', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, WithLp.linearEquiv_symm_apply,
      Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, WithLp.addEquiv_symm_apply
    ]
    ring
  rw [funext h_linear]
  exact L.contDiff

end LeanSharp
