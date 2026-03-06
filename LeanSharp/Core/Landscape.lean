/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The Mathematical Landscape

This module formalizes the parameter space and core calculus operators for
Sharpness-Aware Minimization (SAM).

## Main definitions

* `W`: The parameter space $\mathbb{R}^d$, represented as a Euclidean space.
* `gradient`: The gradient of a loss function, defined via the Riesz representation.
* `hessian`: The Hessian operator, defined as the derivative of the gradient.

## Main theorems

* `hessian_symmetric`: Proves that the Hessian is a self-adjoint operator for C² functions.

## Implementation notes

Since weights are generally vectors in `ℝ^d`, we use `EuclideanSpace ℝ (Fin d)`.
The gradient is computed as the Riesz representation `InnerProductSpace.toDual.symm`
of the Fréchet derivative.

### Functional Analysis (Sobolev Spaces)

We are transitioning the project foundations to rely on Sobolev spaces
(specifically $H^1$ and $H^2$) for regularity, rather than just $C^k$.
This allows analyzing modern ML functions which may lack global $C^2$ smoothness.
-/

namespace LeanSharp

variable {d : ℕ} [Fact (0 < d)]

/-- The parameter space $W = \mathbb{R}^d$, represented as a Euclidean space. -/
abbrev W (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The gradient of a loss function at point `w`.
Defined as the Riesz representation of the Fréchet derivative. -/
noncomputable def gradient (L : W d → ℝ) (w : W d) : W d :=
  (InnerProductSpace.toDual ℝ (W d)).symm (fderiv ℝ L w)

/-- The Hessian operator ∇²L(w) is the derivative of the gradient.
It is a continuous linear map from the parameter space to itself: $W \toL[ℝ] W$. -/
noncomputable def hessian (L : W d → ℝ) (w : W d) : W d →L[ℝ] W d :=
  fderiv ℝ (gradient L) w

/-- A function $L: W \to \mathbb{R}$ has an $L_2$-integrable gradient if
$\int_W \|\text{gradient } L(w)\|_2^2 dw < \infty$. -/
def is_L2_integrable (L : W d → ℝ) : Prop :=
  ∃ _ : MeasureTheory.MeasureSpace (W d),
    MeasureTheory.Integrable (fun w => ‖gradient L w‖^2)

/-- A loss function is "Sobolev Regular" if it belongs to $H^1(W)$,
meaning its value and gradient are both $L_2$-integrable. -/
def is_sobolev_regular (L : W d → ℝ) : Prop :=
  ∃ _ : MeasureTheory.MeasureSpace (W d),
    MeasureTheory.Integrable L ∧ is_L2_integrable L

section NoDimFact
omit [Fact (0 < d)]

/-- The Hessian is symmetric (self-adjoint) for C² loss functions.
Proved via `second_derivative_symmetric` (Schwarz's Theorem) from Mathlib.

Requires: `L` everywhere Fréchet-differentiable (`h_diff`) and `fderiv ℝ L`
differentiable at `w` (`h_grad_diff`). Both hold for any C² loss function. -/
theorem hessian_symmetric (L : W d → ℝ) (w : W d)
    (h_diff : ∀ p : W d, HasFDerivAt L (fderiv ℝ L p) p)
    (h_grad_diff : HasFDerivAt (fderiv ℝ L) (fderiv ℝ (fderiv ℝ L) w) w) :
    (hessian L w).toLinearMap.IsSymmetric := by
  intro x y
  -- Schwarz: (D²L)(w)(x)(y) = (D²L)(w)(y)(x)
  have h_sym : ((fderiv ℝ (fderiv ℝ L) w) x) y = ((fderiv ℝ (fderiv ℝ L) w) y) x :=
    second_derivative_symmetric h_diff h_grad_diff x y
  -- hessian equals (toDual.symm CLM) ∘L D²L(w)
  have h_grad_hasFDeriv : HasFDerivAt (gradient L)
      ((InnerProductSpace.toDual ℝ (W d)).symm.toContinuousLinearMap ∘L fderiv ℝ (fderiv ℝ L) w)
      w := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (W d)).symm.hasFDerivAt.comp w h_grad_diff
  have h_hess_eq : hessian L w =
      (InnerProductSpace.toDual ℝ (W d)).symm.toContinuousLinearMap ∘L
        fderiv ℝ (fderiv ℝ L) w :=
    h_grad_hasFDeriv.fderiv
  rw [h_hess_eq]
  simp only [ContinuousLinearMap.coe_comp, LinearMap.coe_toContinuousLinearMap,
             LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
             LinearIsometryEquiv.coe_toLinearEquiv]
  have key : ∀ (φ : W d →L[ℝ] ℝ) (z : W d),
      @inner ℝ _ _ ((InnerProductSpace.toDual ℝ (W d)).symm φ) z = φ z := by
    intro φ z
    rw [← InnerProductSpace.toDual_apply_apply (𝕜 := ℝ)]
    simp [LinearIsometryEquiv.apply_symm_apply]
  rw [key, real_inner_comm, key]
  exact h_sym

end NoDimFact

end LeanSharp
