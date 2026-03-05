import LeanSharp.Landscape
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Sharpness-Aware Minimization (SAM)

In this file, we define the SAM objective and the perturbation vector.
SAM seeks to find a parameter `w` that minimizes the maximum loss within
a neighborhood of radius `ρ`.

The objective is:
  min_w max_{||ε||₂ ≤ ρ} L(w + ε)
-/

variable {d : ℕ}
-- `W` is already EuclideanSpace ℝ (Fin d) from Landscape.lean

/-- The SAM perturbation neighborhood. We consider all vectors `ε` such that
    the L2 norm metric distance `dist 0 ε ≤ ρ`. -/
def perturbation_neighborhood (ρ : ℝ) : Set (W d) :=
  Metric.closedBall 0 ρ

/-- In SAM, the optimal perturbation `ε*(w)` is the one that maximizes `L(w + ε)`.
    To formalize this generically without computing the exact `sup`, we can define
    the SAM objective as the supremum over the closed ball. -/
noncomputable def sam_objective (L : W d → ℝ) (w : W d) (ρ : ℝ) : ℝ :=
  sSup (L '' ((fun ε => w + ε) '' perturbation_neighborhood ρ))

/-
  Practically, SAM approximates this by taking a first-order Taylor expansion
  around `w`:
    L(w + ε) ≈ L(w) + εᵀ ∇L(w)

  This gives the closed-form dual-norm solution for the perturbation:
    ε*(w) = ρ * ∇L(w) / ||∇L(w)||₂

  We define the Riesz Representation of the gradient here to formalize this.
-/

/-- The Riesz representation of the Fréchet derivative of `L` at `w`.
    This represents the gradient vector `∇L(w)` in the space `W`. -/
noncomputable def gradient (L : W d → ℝ) (w : W d) : W d :=
  InnerProductSpace.toDual ℝ (W d) |>.symm (fderiv ℝ L w)

/-- Property that `w_star` is a critical point (optimum) of `L`. -/
def is_optimum (L : W d → ℝ) (w_star : W d) : Prop :=
  gradient L w_star = 0

/-- The exact first-order approximation perturbation `ε*(w)`. -/
noncomputable def sam_perturbation (L : W d → ℝ) (w : W d) (ρ : ℝ) : W d :=
  let g := gradient L w
  let norm_g := ‖g‖
  if norm_g = 0 then 0 else (ρ / norm_g) • g
