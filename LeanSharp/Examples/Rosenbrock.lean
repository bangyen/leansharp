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
Benchmark landscape with explicit gradient formulas for end-to-end certification.

## Main Definitions
* `L_rosenbrock`.
* `exactGradientRosenbrock`.

## Main Theorems
* `hasFDerivAt_rosenbrock`.
* `gradient_rosenbrock_eq`.
-/

namespace LeanSharp

/-- Rosenbrock function: $L(x) = (1 - x.ofLp 0)^2 + 100(x.ofLp 1 - x.ofLp 0^2)^2$. -/
noncomputable def L_rosenbrock (x : W (Fin 2)) : ℝ :=
  (1 - x.ofLp 0)^2 + 100 * (x.ofLp 1 - (x.ofLp 0)^2)^2

/-- Analytical gradient of the Rosenbrock function. -/
noncomputable def exactGradientRosenbrock (x : W (Fin 2)) : W (Fin 2) :=
  let x0 := x.ofLp 0; let x1 := x.ofLp 1
  (WithLp.equiv 2 _).symm fun i =>
    if i = 0 then -2 * (1 - x0) - 400 * x0 * (x1 - x0^2)
    else 200 * (x1 - x0^2)

/-- **Rosenbrock Gradient Verification**: matches the Fréchet derivative. -/
theorem hasFDerivAt_rosenbrock (x : W (Fin 2)) :
    HasFDerivAt L_rosenbrock (InnerProductSpace.toDual ℝ (W (Fin 2))
    (exactGradientRosenbrock x)) x := by
  classical
  let proj0 : W (Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) 0
  let proj1 : W (Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) 1
  -- Term 1: (1 - x.ofLp 0)^2
  have h0 : HasFDerivAt (fun x : W (Fin 2) => x.ofLp 0) proj0 x := PiLp.hasFDerivAt_apply 2 x 0
  have h1 : HasFDerivAt (fun x => 1 - x.ofLp 0) (-proj0) x := by
    have h := (hasFDerivAt_const (1 : ℝ) x).sub h0; rw [zero_sub] at h; exact h
  have h1s : HasFDerivAt (fun x => (1 - x.ofLp 0)^2) ((2 * (1 - x.ofLp 0)) • (-proj0)) x := by
    convert h1.pow 2 using 1; · simp only [nsmul_eq_mul]; ring_nf
  -- Term 2: 100 * (x.ofLp 1 - x.ofLp 0^2)^2
  have hx0s : HasFDerivAt (fun x => (x.ofLp 0)^2) ((2 * x.ofLp 0) • proj0) x := by
    convert h0.pow 2 using 1; · simp only [nsmul_eq_mul]; ring_nf
  have h1p : HasFDerivAt (fun x : W (Fin 2) => x.ofLp 1) proj1 x := PiLp.hasFDerivAt_apply 2 x 1
  have hdf : HasFDerivAt (fun x => x.ofLp 1 - (x.ofLp 0)^2) (proj1 - (2 * x.ofLp 0) • proj0) x :=
    h1p.sub hx0s
  have h100s : HasFDerivAt (fun x => 100 * (x.ofLp 1 - (x.ofLp 0)^2)^2)
      ((100 * (2 * (x.ofLp 1 - x.ofLp 0^2))) • (proj1 - (2 * x.ofLp 0) • proj0)) x := by
    convert (hdf.pow 2).const_smul (100 : ℝ) using 1
    · simp only [nsmul_eq_mul, smul_smul]; congr 1; ring_nf
  -- Total
  convert h1s.add h100s; ext v
  simp only [InnerProductSpace.toDual_apply_apply, smul_neg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_sub', Pi.sub_apply, inner, RCLike.inner_apply, conj_trivial, mul_ite,
    Fin.sum_univ_two, ↓reduceIte, one_ne_zero, PiLp.proj_apply, proj0, proj1,
    exactGradientRosenbrock, WithLp.equiv_symm_apply]; ring

/-- Analytical gradient matches the Fréchet derivative. -/
theorem gradient_rosenbrock_eq (x : W (Fin 2)) :
    gradient L_rosenbrock x = exactGradientRosenbrock x := by
  have h := hasFDerivAt_rosenbrock x; rw [gradient, h.fderiv, LinearIsometryEquiv.symm_apply_apply]

end LeanSharp
