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
## The Theorem Statement and Proof

We prove the SAM generalization bound from two structural assumptions:
1. A **generalization gap** bound: `L_D(w) ≤ L_S(w) + h(‖w‖²/ρ²)` (from PAC-Bayes theory)
2. The **monotonicity** of `h`.

Since `sam_empirical_max(S, w, ρ) = max_{‖ε‖≤ρ} L_S(w+ε) ≥ L_S(w)` 
(zero-perturbation is feasible), we get:
`L_D(w) ≤ L_S(w) + h(‖w‖²/ρ²) ≤ sam_empirical_max + h(‖w‖²/ρ²)`.
-/

/-- The SAM Generalization Bound Theorem condition. -/
def sam_generalization_bound_holds {n : ℕ} (S : Fin n → DataPoint) (ρ : ℝ) : Prop :=
  ∀ w : W d, ρ > 0 →
    L_D w ≤ sam_empirical_max DataPoint sample_loss S w ρ + h (‖w‖^2 / ρ^2)

/-- The SAM generalization bound holds given a standard generalization gap assumption.
    We prove that `sam_empirical_max ≥ L_S(w)`, so the SAM bound dominates the
    ordinary Rademacher / PAC-Bayes generalization bound. -/
theorem sam_bound_from_gap {n : ℕ} (S : Fin n → DataPoint)
    -- The standard generalization gap: L_D(w) ≤ L_S(w) + h(‖w‖²/ρ²)
    (h_gap : ∀ (w : W d) (r : ℝ), r > 0 →
        L_D w ≤ empirical_risk DataPoint sample_loss S w + h (‖w‖ ^ 2 / r ^ 2))
    -- h is monotone (so larger SAM objective → larger pacing)
    (_h_mono : Monotone h)
    -- Boundedness of empirical risk on the perturbation ball 
    -- (follows from continuity + compactness)
    (h_bdd : ∀ (w : W d) (r : ℝ), BddAbove
        (empirical_risk DataPoint sample_loss S ''
          ((fun ε => w + ε) '' Metric.closedBall 0 r))) :
    sam_generalization_bound_holds DataPoint sample_loss L_D h S ρ := by
  intro w hρ
  -- The empirical risk at zero-perturbation is a lower bound for sam_empirical_max
  have h_sam_ge : empirical_risk DataPoint sample_loss S w ≤
      sam_empirical_max DataPoint sample_loss S w ρ := by
    unfold sam_empirical_max sam_objective perturbation_neighborhood
    -- w = w + 0, and 0 ∈ closedBall 0 ρ since ρ > 0
    have h_mem : empirical_risk DataPoint sample_loss S w ∈
        empirical_risk DataPoint sample_loss S ''
          ((fun ε => w + ε) '' Metric.closedBall 0 ρ) := by
      refine ⟨w, ⟨0, ?_, by simp⟩, rfl⟩
      simp [Metric.mem_closedBall, le_of_lt hρ]
    exact le_csSup (h_bdd w ρ) h_mem
  -- Combine: L_D(w) ≤ L_S(w) + h(...) ≤ sam_max + h(...)
  linarith [h_gap w ρ hρ]

