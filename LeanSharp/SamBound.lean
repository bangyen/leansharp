import LeanSharp.Landscape
import LeanSharp.Sam
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

namespace LeanSharp

variable {d : ℕ} [Fact (0 < d)]

-- We assume the existence of a true population risk function over the parameter space.
variable (L_D : W d → ℝ)

-- We assume the existence of an empirical risk function over the parameter space.
variable (L_S : W d → ℝ)

-- The pacing function h : R_{>0} -> R_{>0} defined by Foret et al.
variable (h : ℝ → ℝ)

/-- The maximal empirical risk in the $\rho$-neighborhood.
    This uses the exact `sam_objective` we formalized in Phase 0. -/
noncomputable def sam_empirical_max (w : W d) (ρ : ℝ) : ℝ :=
  sam_objective L_S w ρ

/-- The SAM Generalization Bound Theorem condition.
    States that with high probability, the population risk is bounded by the SAM objective. -/
def sam_generalization_bound_holds (ρ : ℝ) : Prop :=
  ∀ w : W d, ρ > 0 →
    L_D w ≤ sam_empirical_max L_S w ρ + h (‖w‖^2 / ρ^2)

section NoDimFact
omit [Fact (0 < d)]

/-- Theorem: The SAM generalization bound holds given a standard generalization gap assumption.
    We prove that `sam_empirical_max ≥ L_S(w)`, so the SAM bound dominates the
    ordinary Rademacher / PAC-Bayes generalization bound. -/
theorem sam_bound_from_gap {ρ : ℝ}
    (h_gap : ∀ (w : W d) (r : ℝ), r > 0 →
        L_D w ≤ L_S w + h (‖w‖ ^ 2 / r ^ 2))
    (_h_mono : Monotone h)
    (h_bdd : ∀ (w : W d) (r : ℝ), BddAbove
        (L_S '' ((fun ε => w + ε) '' Metric.closedBall 0 r))) :
    sam_generalization_bound_holds L_D L_S h ρ := by
  intro w hρ
  have h_sam_ge : L_S w ≤ sam_empirical_max L_S w ρ := by
    unfold sam_empirical_max sam_objective perturbation_neighborhood
    have h_mem : L_S w ∈ L_S '' ((fun ε => w + ε) '' Metric.closedBall 0 ρ) := by
      refine ⟨w, ⟨0, ?_, by simp⟩, rfl⟩
      simp [Metric.mem_closedBall, le_of_lt hρ]
    exact le_csSup (h_bdd w ρ) h_mem
  have h_gap_spec := h_gap w ρ hρ
  linarith [h_gap_spec, h_sam_ge]

end NoDimFact

end LeanSharp
