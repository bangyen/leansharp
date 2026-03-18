/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.Landscape
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rosenbrock Example

This module exists to provide a nonlinear benchmark landscape with explicit
gradient formulas, enabling end-to-end validation beyond quadratic toy models.

## Definitions

* `L_rosenbrock`.
* `exactGradientRosenbrock`.

## Theorems

* `hasFDerivAt_rosenbrock`.
* `gradient_rosenbrock_eq`.
-/

namespace LeanSharp

/-- The Rosenbrock function: $L(x, y) = (1 - x)^2 + 100(y - x^2)^2$. -/
noncomputable def L_rosenbrock (x : W (Fin 2)) : ℝ :=
  let x₀ := x.ofLp 0
  let x₁ := x.ofLp 1
  (1 - x₀)^2 + 100 * (x₁ - x₀^2)^2

/-- Analytical gradient of the Rosenbrock function. -/
noncomputable def exactGradientRosenbrock (x : W (Fin 2)) : W (Fin 2) :=
  let x₀ := x.ofLp 0
  let x₁ := x.ofLp 1
  (WithLp.equiv 2 _).symm fun i =>
    if i = 0 then
      -2 * (1 - x₀) - 400 * x₀ * (x₁ - x₀^2)
    else
      200 * (x₁ - x₀^2)

/-- **Rosenbrock Gradient Verification**: Confirm that the analytical gradient
    matches the Fréchet derivative. -/
theorem hasFDerivAt_rosenbrock (x : W (Fin 2)) :
    HasFDerivAt L_rosenbrock
    (InnerProductSpace.toDual ℝ (W (Fin 2))
    (exactGradientRosenbrock x)) x := by
  dsimp only [
    exactGradientRosenbrock,
    Fin.isValue,
    WithLp.equiv_symm_apply
  ]
  let x₀ := x.ofLp 0
  let x₁ := x.ofLp 1
  -- Projections are differentiable
  let proj0 : W (Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  let proj1 : W (Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have h0 : HasFDerivAt (fun (x : W (Fin 2)) => x.ofLp 0) proj0 x :=
    PiLp.hasFDerivAt_apply 2 x 0
  have h1 : HasFDerivAt (fun (x : W (Fin 2)) => x.ofLp 1) proj1 x :=
    PiLp.hasFDerivAt_apply 2 x 1
  -- (1 - x₀)
  have h1x0 : HasFDerivAt (fun x => (1 : ℝ) - x.ofLp 0) (-proj0) x := by
    have h_const :
      HasFDerivAt (fun _ => (1 : ℝ)) (0 : W (Fin 2) →L[ℝ] ℝ) x := hasFDerivAt_const (1 : ℝ) x
    have h_sub := h_const.sub h0
    rw [zero_sub] at h_sub; exact h_sub
  -- (1 - x₀)^2
  have h1x0_sq : HasFDerivAt (fun x => (1 - x.ofLp 0)^2) ((2 * (1 - x₀)) • (-proj0)) x := by
    have h_pow := h1x0.pow 2
    dsimp only [Fin.isValue, x₀]; convert h_pow using 1; simp only [
      Fin.isValue,
      smul_neg,
      Nat.add_one_sub_one,
      pow_one,
      nsmul_eq_mul,
      Nat.cast_ofNat
    ]
  -- x₀^2
  have hx0_sq : HasFDerivAt (fun x => x.ofLp 0^2) ((2 * x₀) • proj0) x := by
    have h_pow := h0.pow 2
    dsimp only [Fin.isValue, x₀]; convert h_pow using 1; simp only [
      Fin.isValue,
      Nat.add_one_sub_one,
      pow_one,
      nsmul_eq_mul,
      Nat.cast_ofNat
    ]
  -- (x₁ - x₀^2)
  have hdiff :
    HasFDerivAt (fun x => x.ofLp 1 - x.ofLp 0^2) (proj1 - (2 * x₀) • proj0) x := h1.sub hx0_sq
  -- 100 * (x₁ - x₀^2)^2
  have h100diff_sq :
    HasFDerivAt (fun x => (100 : ℝ) * (x.ofLp 1 - x.ofLp 0^2)^2)
      (((100 : ℝ) * (2 * (x₁ - x₀^2))) • (proj1 - (2 * x₀) • proj0)) x := by
    have h_pow := hdiff.pow 2
    have h_smul := h_pow.const_smul (100 : ℝ)
    convert h_smul using 1
    · ext; dsimp only [
      Fin.isValue,
      ContinuousLinearMap.coe_smul',
      ContinuousLinearMap.coe_sub',
      Pi.smul_apply,
      Pi.sub_apply,
      smul_eq_mul,
      Nat.add_one_sub_one,
      x₁,
      x₀
    ]; ring
  -- Total sum
  have h_total := h1x0_sq.add h100diff_sq
  simp only [Fin.isValue, neg_mul] at h_total ⊢
  -- Compare derivatives
  convert h_total
  ext v
  simp only [
    Fin.isValue,
    InnerProductSpace.toDual_apply_apply,
    smul_neg,
    ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_smul',
    Pi.smul_apply,
    smul_eq_mul,
    ContinuousLinearMap.coe_sub',
    Pi.sub_apply
  ]
  -- EuclideanSpace inner product
  simp only [
    inner,
    Fin.isValue,
    RCLike.inner_apply,
    conj_trivial,
    mul_ite,
    Fin.sum_univ_two,
    ↓reduceIte,
    one_ne_zero,
    PiLp.proj_apply,
    proj0,
    proj1
  ]
  ring

/-- Formal theorem confirming the correctness of the analytical gradient. -/
theorem gradient_rosenbrock_eq (x : W (Fin 2)) :
    gradient L_rosenbrock x = exactGradientRosenbrock x := by
  have h := hasFDerivAt_rosenbrock x
  rw [
    gradient,
    h.fderiv,
    LinearIsometryEquiv.symm_apply_apply
  ]

end LeanSharp
