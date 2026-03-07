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

/-- **Riesz Inner Product Identity**: The inner product with the Riesz representation
of a linear form `φ` is simply the evaluation of `φ`. -/
lemma inner_riesz_symm_apply (φ : W d →L[ℝ] ℝ) (z : W d) :
    inner ℝ ((InnerProductSpace.toDual ℝ (W d)).symm φ) z = φ z := by
  rw [← InnerProductSpace.toDual_apply_apply (𝕜 := ℝ)]
  simp [LinearIsometryEquiv.apply_symm_apply]

/-- **Hessian Riesz Composition Definition**: Relates the Hessian operator
to the second Fréchet derivative via the Riesz isometry. -/
lemma hessian_def_riesz_comp (L : W d → ℝ) (w : W d)
    (h_grad_diff : HasFDerivAt (fderiv ℝ L) (fderiv ℝ (fderiv ℝ L) w) w) :
    hessian L w = (InnerProductSpace.toDual ℝ (W d)).symm.toContinuousLinearMap ∘L
        fderiv ℝ (fderiv ℝ L) w := by
  have h_comp : HasFDerivAt (gradient L)
      ((InnerProductSpace.toDual ℝ (W d)).symm.toContinuousLinearMap ∘L
        fderiv ℝ (fderiv ℝ L) w) w := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (W d)).symm.hasFDerivAt.comp w h_grad_diff
  exact h_comp.fderiv

/-- **Hessian Symmetry Reduction**: Reduces the self-adjointness of the Hessian
to the symmetry of the second Fréchet derivative. -/
lemma hessian_symmetry_reduction (L : W d → ℝ) (w : W d)
    (H : W d →L[ℝ] W d →L[ℝ] ℝ)
    (h_hess : hessian L w = (InnerProductSpace.toDual ℝ (W d)).symm.toContinuousLinearMap ∘L H)
    (h_sym : ∀ x y, (H x) y = (H y) x) :
    (hessian L w).toLinearMap.IsSymmetric := by
  intro x y
  rw [h_hess]
  simp only [ContinuousLinearMap.coe_comp, LinearMap.coe_toContinuousLinearMap,
             LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
             LinearIsometryEquiv.coe_toLinearEquiv]
  rw [inner_riesz_symm_apply, real_inner_comm, inner_riesz_symm_apply]
  exact h_sym x y

/-- The Hessian is symmetric (self-adjoint) for C² loss functions.
Proved via `second_derivative_symmetric` (Schwarz's Theorem) from Mathlib.

Requires: `L` everywhere Fréchet-differentiable (`h_diff`) and `fderiv ℝ L`
differentiable at `w` (`h_grad_diff`). Both hold for any C² loss function. -/
theorem hessian_symmetric (L : W d → ℝ) (w : W d)
    (h_diff : ∀ p : W d, HasFDerivAt L (fderiv ℝ L p) p)
    (h_grad_diff : HasFDerivAt (fderiv ℝ L) (fderiv ℝ (fderiv ℝ L) w) w) :
    (hessian L w).toLinearMap.IsSymmetric := by
  -- Step 1: Schwarz's Theorem provides the symmetry of the Fréchet derivative
  have h_sym : ∀ x y, ((fderiv ℝ (fderiv ℝ L) w) x) y = ((fderiv ℝ (fderiv ℝ L) w) y) x :=
    fun x y => second_derivative_symmetric h_diff h_grad_diff x y
  -- Step 2: Relate the Hessian to the Fréchet derivative
  have h_hess_eq := hessian_def_riesz_comp L w h_grad_diff
  -- Step 3: Use the symmetry reduction helper
  exact hessian_symmetry_reduction L w (fderiv ℝ (fderiv ℝ L) w) h_hess_eq h_sym

/-- **Descent Step Quadratic Expansion**: The standard squared norm identity for a
descent step $w - ηg$ relative to a target $w^*$. -/
lemma norm_descent_step_sq (w w_star g : W d) (η : ℝ) :
    ‖(w - η • g) - w_star‖^2 = ‖w - w_star‖^2 - 2 * η * inner ℝ g (w - w_star) + η^2 * ‖g‖^2 := by
  have hrw : (w - η • g) - w_star = (w - w_star) - η • g := by abel
  rw [hrw, norm_sub_sq_real, inner_smul_right, real_inner_comm]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- **Squared Norm of Difference with Scalar Multiple**:
‖a - ηb‖² = ‖a‖² - 2η⟨b, a⟩ + η²‖b‖². -/
lemma norm_sub_smul_sq (a b : W d) (η : ℝ) :
    ‖a - η • b‖^2 = ‖a‖^2 - 2 * η * inner ℝ b a + η^2 * ‖b‖^2 := by
  rw [norm_sub_sq_real, inner_smul_right, real_inner_comm]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

end NoDimFact

end LeanSharp
