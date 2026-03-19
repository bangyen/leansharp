/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The Mathematical Landscape

This module formalizes the parameter space and core calculus operators for
Sharpness-Aware Minimization (SAM).

## Main Definitions
* `W`: The parameter space $\mathbb{R}^d$, represented as a Euclidean space.
* `gradient`: The gradient of a loss function, defined via the Riesz representation.
* `hessian`: The Hessian operator, defined as the derivative of the gradient.
* `TwiceDifferentiable`: Bundles a function $L$ with its second-order regularity properties.

## Main Theorems
* `hessian_symmetric`: Proves that the Hessian is a self-adjoint operator for C² functions.

## Implementation notes

Since weights are generally vectors in `ℝ^d`, we use `EuclideanSpace ℝ (ι)`.
The gradient is computed as the Riesz representation `InnerProductSpace.toDual.symm`
of the Fréchet derivative.

### Research Note: Functional Analysis (Sobolev Spaces)

Future transitions of the project foundations may rely on Sobolev spaces
(specifically $H^1$ and $H^2$) for regularity, rather than just $C^k$.
This would allow analyzing modern ML functions which may lack global $C^2$ smoothness.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- The parameter space $W = \mathbb{R}^d$, represented as a Euclidean space. -/
abbrev W (ι : Type*) := EuclideanSpace ℝ ι

/-- The gradient of a loss function at point `w`.
Defined as the Riesz representation of the Fréchet derivative. -/
noncomputable def gradient (L : W ι → ℝ) (w : W ι) : W ι :=
  (InnerProductSpace.toDual ℝ (W ι)).symm (fderiv ℝ L w)

/-- The Hessian operator ∇²L(w) is the derivative of the gradient.
It is a continuous linear map from the parameter space to itself: $W \toL[ℝ] W$. -/
noncomputable def hessian (L : W ι → ℝ) (w : W ι) : W ι →L[ℝ] W ι :=
  fderiv ℝ (gradient L) w

/-- **Hessian Riesz Composition Definition**: Relates the Hessian operator
to the second Fréchet derivative via the Riesz isometry. -/
private lemma hessian_def_riesz_comp (L : W ι → ℝ) (w : W ι)
    (h_grad_diff : HasFDerivAt (fderiv ℝ L) (fderiv ℝ (fderiv ℝ L) w) w) :
    hessian L w = (InnerProductSpace.toDual ℝ (W ι)).symm.toContinuousLinearMap ∘L
        fderiv ℝ (fderiv ℝ L) w :=
  ((InnerProductSpace.toDual ℝ (W ι)).symm.hasFDerivAt.comp w h_grad_diff).fderiv

/-- **Hessian Symmetry Reduction**: Reduces the self-adjointness of the Hessian
to the symmetry of the second Fréchet derivative. -/
private lemma hessian_symmetry_reduction (L : W ι → ℝ) (w : W ι)
    (H : W ι →L[ℝ] W ι →L[ℝ] ℝ)
    (h_hess : hessian L w = (InnerProductSpace.toDual ℝ (W ι)).symm.toContinuousLinearMap ∘L H)
    (h_sym : ∀ x y, (H x) y = (H y) x) :
    (hessian L w).toLinearMap.IsSymmetric := by
  intro x y
  rw [h_hess]
  simp only [
    ContinuousLinearMap.coe_comp,
    LinearMap.coe_toContinuousLinearMap,
    LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap,
    LinearIsometryEquiv.coe_toLinearEquiv
  ]
  -- Inlined: the inner product with the Riesz representation is the evaluation.
  have h_riesz (φ : W ι →L[ℝ] ℝ) (z : W ι) :
      inner ℝ ((InnerProductSpace.toDual ℝ (W ι)).symm φ) z = φ z := by
    rw [
      ← InnerProductSpace.toDual_apply_apply (𝕜 := ℝ),
      LinearIsometryEquiv.apply_symm_apply
    ]
  rw [h_riesz, real_inner_comm, h_riesz]
  exact h_sym x y

/-- A structure bundling a function $L$ with its second-order regularity properties. -/
structure TwiceDifferentiable (ι : Type*) [Fintype ι] where
  /-- The underlying loss function. -/
  toFun : W ι → ℝ
  /-- Proof that the function is twice continuously differentiable everywhere. -/
  differentiable : ContDiff ℝ 2 toFun

/-- The Hessian is symmetric (self-adjoint) for C² loss functions.
Proved via `second_derivative_symmetric` (Schwarz's Theorem) from Mathlib. -/
theorem hessian_symmetric (L : TwiceDifferentiable ι) (w : W ι) :
    (hessian L.toFun w).toLinearMap.IsSymmetric := by
  have h' : ContDiff ℝ (1 + 1) L.toFun := L.differentiable
  have hd1 : ∀ p, HasFDerivAt L.toFun (fderiv ℝ L.toFun p) p :=
    fun p => ((contDiff_succ_iff_fderiv.mp h').left p).hasFDerivAt
  have hd2_cont : ContDiff ℝ 1 (fderiv ℝ L.toFun) := (contDiff_succ_iff_fderiv.mp h').2.2
  have hd2 : ∀ p, DifferentiableAt ℝ (fderiv ℝ L.toFun) p :=
    fun p => (ContDiff.differentiable hd2_cont (by decide) p)
  exact hessian_symmetry_reduction L.toFun w (fderiv ℝ (fderiv ℝ L.toFun) w)
    (hessian_def_riesz_comp L.toFun w (hd2 w).hasFDerivAt)
    (fun x y => second_derivative_symmetric hd1 (hd2 w).hasFDerivAt x y)

/-- **Squared Norm of Difference with Scalar Multiple**:
‖a - ηb‖² = ‖a‖² - 2η⟨b, a⟩ + η²‖b‖². -/
lemma norm_sub_smul_sq (a b : W ι) (η : ℝ) :
    ‖a - η • b‖^2 = ‖a‖^2 - 2 * η * inner ℝ b a + η^2 * ‖b‖^2 := by
  rw [
    norm_sub_sq_real,
    inner_smul_right,
    real_inner_comm,
    norm_smul,
    Real.norm_eq_abs,
    mul_pow,
    sq_abs
  ]
  ring

/-- **Descent Step Quadratic Expansion**: The standard squared norm identity for a
descent step $w - ηg$ relative to a target $w^*$. -/
lemma norm_descent_step_sq (w w_star g : W ι) (η : ℝ) :
  ‖(w - η • g) - w_star‖^2 =
    ‖w - w_star‖^2 - 2 * η * inner ℝ g (w - w_star) + η^2 * ‖g‖^2 := by
  have : (w - η • g) - w_star = (w - w_star) - η • g := by abel
  rw [this, norm_sub_smul_sq]

end LeanSharp
