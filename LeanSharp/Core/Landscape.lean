import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The Mathematical Landscape

In order to formulate Sharpness-Aware Minimization (SAM), we need to formalize:
1. The parameter space `W` (which is typically a Euclidean space like ℝ^d).
2. The loss function `L : W → ℝ`.

Since weights are generally vectors in `ℝ^d`, we use `EuclideanSpace ℝ (Fin d)`.
-/

/-
  To define SAM, we need the gradient of `L`. In Lean, the Fréchet derivative
  of `L` at `w` is `fderiv ℝ L w`. Since `W` is a Hilbert space, the gradient
  is the Riesz representation of this derivative.
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
