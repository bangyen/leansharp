import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

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

/- 
  Using the Riesz representation theorem, we can define the gradient `∇L(w)`
  as a vector in `W` rather than a linear map. Mathlib provides this via 
  `InnerProductSpace.toDual`.

  For simplicity in standard optimization contexts, we will often define
  formulas that apply a perturbation abstractly, assuming `L` is differentiable.
-/

-- A perturbation vector ε in the parameter space.
variable (ε : W d)
