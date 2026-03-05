import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# The Mathematical Landscape

In order to formulate Sharpness-Aware Minimization (SAM), we need to formalize:
1. The parameter space `W` (which is typically a Euclidean space like ℝ^d).
2. The loss function `L : W → ℝ`.

Since weights are generally vectors in `ℝ^d`, we use `EuclideanSpace ℝ (Fin d)`.
-/

variable {d : ℕ}

/-- The parameter space `W` of the neural network, represented as `ℝ^d`.
    This automatically comes with an inner product, norm, and metric space structure
    from `Mathlib.Analysis.InnerProductSpace.PiL2`. -/
abbrev W (d : ℕ) := EuclideanSpace ℝ (Fin d)

-- A generic loss function over the parameter space W.
variable (L : W d → ℝ)

-- We typically require that the loss function is differentiable everywhere
-- so that we can compute the gradient ∇L(w).
variable (h_diff : Differentiable ℝ L)

/-
  To define SAM, we need the gradient of `L`. In Lean, the Fréchet derivative
  of `L` at `w` is `fderiv ℝ L w`. Since `W` is a Hilbert space, the gradient
  is the Riesz representation of this derivative.
-/

namespace LeanSharp

variable {d : ℕ} [Fact (0 < d)]

/-- The parameter space $W = \mathbb{R}^d$, represented as a Euclidean space. -/
abbrev W (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable instance : NormedAddCommGroup (W d) := by unfold W; infer_instance
noncomputable instance : InnerProductSpace ℝ (W d) := by unfold W; infer_instance
noncomputable instance : FiniteDimensional ℝ (W d) := by unfold W; infer_instance

/-- A loss function is a differentiable mapping from parameter space to Reals. -/
def LossFunction (d : ℕ) := W d → ℝ

/-- The Fréchet derivative of L at a point w. -/
noncomputable def L_deriv (L : W d → ℝ) (w : W d) : W d →L[ℝ] ℝ :=
  fderiv ℝ L w

/-- The gradient of a loss function at point `w`.
    Defined as the Riesz representation of the Fréchet derivative. -/
noncomputable def gradient (L : W d → ℝ) (w : W d) : W d :=
  (InnerProductSpace.toDual ℝ (W d)).symm (fderiv ℝ L w)

/-- The Hessian operator ∇²L(w) is the derivative of the gradient.
    It is a continuous linear map from the parameter space to itself: $W \toL[ℝ] W$. -/
noncomputable def hessian (L : W d → ℝ) (w : W d) : W d →L[ℝ] W d :=
  fderiv ℝ (gradient L) w

/-- Axiom: The Hessian is symmetric (self-adjoint).
    This follows from Schwarz's Theorem for $C^2$ functions. -/
axiom hessian_symmetric (L : W d → ℝ) (w : W d) :
  (hessian L w).toLinearMap.IsSymmetric

end LeanSharp

-- A perturbation vector ε in the parameter space.
variable {d : ℕ} [Fact (0 < d)] (ε : LeanSharp.W d)
