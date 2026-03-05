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
  is the Riesz representation of this derivative. However, we can also work
  directly with the directional derivative or the Fréchet derivative `fderiv`
  treated as a continuous linear map `W →L[ℝ] ℝ`.
-/

-- The Fréchet derivative of L at a point w.
noncomputable def L_deriv (w : W d) : W d →L[ℝ] ℝ :=
  fderiv ℝ L w

-- A Generic gradient definition using Riesz representation or fderiv
noncomputable def gradient (L : W d → ℝ) (w : W d) : W d :=
  (InnerProductSpace.toDual ℝ (W d)).symm (fderiv ℝ L w)

/-- The Hessian operator ∇²L(w) is the derivative of the gradient.
    It can be viewed as a continuous linear map from the parameter space
    to itself: W →L[ℝ] W. -/
noncomputable def hessian (L : W d → ℝ) (w : W d) : W d →L[ℝ] W d :=
  fderiv ℝ (gradient L) w

/-- We assume the Hessian is symmetric (self-adjoint).
    In standard analysis, this follows from C² smoothness (Schwarz's theorem). -/
axiom hessian_symmetric (L : W d → ℝ) (w : W d) :
  (hessian L w).toLinearMap.IsSymmetric

-- A perturbation vector ε in the parameter space.
variable (ε : W d)
