import LeanSharp.Landscape
import LeanSharp.Sam
import LeanSharp.Stochastics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Phase 3: The SAM Generalization Bound

The core motivation behind Sharpness-Aware Minimization (Foret et al., 2020)
is the theorem that bounds the true population risk $L_D(w)$ by the maximum
empirical risk within a neighborhood, plus a complexity pacing function.

Theorem:
For any $\rho > 0$, with high probability:
$L_\mathcal{D}(w) \le \max_{\|\epsilon\| \le \rho} L_\mathcal{S}(w + \epsilon)
+ h(\|w\|_2^2 / \rho^2)$
-/

variable {d : ℕ} (DataPoint : Type*)
variable (sample_loss : W d → DataPoint → ℝ)

-- We assume the existence of a true population risk function over the parameter space.
-- In real ML theory, this is the expected value of the loss over the true data distribution D.
variable (L_D : W d → ℝ)

-- The pacing function h : R_{>0} -> R_{>0} defined by Foret et al.
-- Typically, h(t) \propto \sqrt{\log(t)}. We define it abstractly here
-- as a strictly monotonically increasing function.
variable (h : ℝ → ℝ)
variable (h_mono : StrictMono h)

/-- For a given dataset `S`, the maximal empirical risk in the $\rho$-neighborhood. 
    This uses the exact `sam_objective` we formalized in Phase 0. -/
noncomputable def sam_empirical_max {n : ℕ} (S : Fin n → DataPoint) (w : W d) (ρ : ℝ) : ℝ :=
  sam_objective (empirical_risk DataPoint sample_loss S) w ρ

/-!
## The Theorem Statement

We now mathematically state the SAM generalization bound.
This proposition asserts that for all parameters `w` and all radii `ρ > 0`,
the population risk is bounded by the empirical SAM objective plus the pacing function.

In a full PhD-level formalization, one would prove this bound from PAC-Bayesian
foundations. Here, we formalize the theorem statement itself as an axiom of the SAM framework.
-/

/-- The SAM Generalization Bound Theorem condition. -/
def sam_generalization_bound_holds {n : ℕ} (S : Fin n → DataPoint) (ρ : ℝ) : Prop :=
  ∀ w : W d, ρ > 0 →
    L_D w ≤ sam_empirical_max DataPoint sample_loss S w ρ + h (‖w‖^2 / ρ^2)

/-
  From this bound, the SAM optimization objective naturally arises:
  Minimize the right hand side via gradient descent.

  RHS = sam_empirical_max + h(‖w‖^2 / ρ^2)
      ≈ L_S(w + ε*) + λ‖w‖^2
      
  Where ε* is the perturbation, and λ is weight decay.
-/
