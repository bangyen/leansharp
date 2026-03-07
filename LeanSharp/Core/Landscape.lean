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
import Mathlib.Probability.Notation

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

open ProbabilityTheory MeasureTheory

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

/-- **Integral Inner Product Identity**: The integral of an inner product with a
constant vector is the inner product of the integral. -/
lemma integral_inner_const {Ω : Type*} [MeasureSpace Ω]
    {f : Ω → W d} (hf : MeasureTheory.Integrable f) (c : W d) :
    (∫ ω, inner ℝ (f ω) c ∂MeasureTheory.volume) = inner ℝ (∫ ω, f ω ∂MeasureTheory.volume) c := by
  have : (fun ω => inner ℝ (f ω) c) = (fun ω => inner ℝ c (f ω)) :=
    by funext ω; rw [real_inner_comm]
  rw [this, integral_inner hf c, real_inner_comm]

/-- **Hessian Riesz Composition Definition**: Relates the Hessian operator
to the second Fréchet derivative via the Riesz isometry. -/
lemma hessian_def_riesz_comp (L : W d → ℝ) (w : W d)
    (h_grad_diff : HasFDerivAt (fderiv ℝ L) (fderiv ℝ (fderiv ℝ L) w) w) :
    hessian L w = (InnerProductSpace.toDual ℝ (W d)).symm.toContinuousLinearMap ∘L
        fderiv ℝ (fderiv ℝ L) w :=
  ((InnerProductSpace.toDual ℝ (W d)).symm.hasFDerivAt.comp w h_grad_diff).fderiv

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
    (hessian L w).toLinearMap.IsSymmetric :=
  hessian_symmetry_reduction L w (fderiv ℝ (fderiv ℝ L) w)
    (hessian_def_riesz_comp L w h_grad_diff)
    (fun x y => second_derivative_symmetric h_diff h_grad_diff x y)

/-- **Squared Norm of Difference with Scalar Multiple**:
‖a - ηb‖² = ‖a‖² - 2η⟨b, a⟩ + η²‖b‖². -/
lemma norm_sub_smul_sq (a b : W d) (η : ℝ) :
    ‖a - η • b‖^2 = ‖a‖^2 - 2 * η * inner ℝ b a + η^2 * ‖b‖^2 := by
  rw [norm_sub_sq_real, inner_smul_right, real_inner_comm]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- **Descent Step Quadratic Expansion**: The standard squared norm identity for a
descent step $w - ηg$ relative to a target $w^*$. -/
lemma norm_descent_step_sq (w w_star g : W d) (η : ℝ) :
    ‖(w - η • g) - w_star‖^2 = ‖w - w_star‖^2 - 2 * η * inner ℝ g (w - w_star) + η^2 * ‖g‖^2 := by
  have : (w - η • g) - w_star = (w - w_star) - η • g := by abel
  rw [this, norm_sub_smul_sq]

/-- **Stochastic Distance Expansion**: The identity for the expected squared distance
after an update step: $𝔼[‖A - η • B‖ ^ 2] = ‖A‖ ^ 2 - 2η⟨𝔼[B], A⟩ +$
$η ^ 2 𝔼[‖B‖ ^ 2]$.
-/
lemma stochastic_dist_expansion {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (A : W d) (B : Ω → W d) (η : ℝ)
    (h_int_B : Integrable B) (h_int_B2 : Integrable (fun ω => ‖B ω‖ ^ 2)) :
    (∫ ω, ‖A - η • B ω‖ ^ 2 ∂volume) =
      ‖A‖ ^ 2 - 2 * η * inner ℝ (∫ ω, B ω ∂volume) A + η^2 * (∫ ω, ‖B ω‖ ^ 2 ∂volume) := by
  have h_int_1 : Integrable (fun ω => ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A) :=
    (integrable_const _).sub (h_int_B.inner_const A |>.const_mul (2 * η))
  have h_int_2 : Integrable (fun ω => η^2 * ‖B ω‖ ^ 2) := h_int_B2.const_mul (η^2)
  calc (∫ ω, ‖A - η • B ω‖ ^ 2 ∂volume)
    _ = ∫ ω, ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A + η^2 * ‖B ω‖ ^ 2 ∂volume := by
        simp_rw [norm_sub_smul_sq]
    _ = (∫ ω, ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A ∂volume) + (∫ ω, η^2 * ‖B ω‖ ^ 2 ∂volume) :=
        integral_add h_int_1 h_int_2
    _ = ‖A‖ ^ 2 - 2 * η * (∫ ω, inner ℝ (B ω) A ∂volume) + η ^ 2 * (∫ ω, ‖B ω‖ ^ 2 ∂volume) := by
        rw [integral_sub (integrable_const _) (h_int_B.inner_const A |>.const_mul (2 * η)),
            integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul]
    _ = ‖A‖ ^ 2 - 2 * η * inner ℝ (∫ ω, B ω ∂volume) A + η ^ 2 * (∫ ω, ‖B ω‖ ^ 2 ∂volume) := by
        rw [integral_inner_const h_int_B A]

end NoDimFact

end LeanSharp
