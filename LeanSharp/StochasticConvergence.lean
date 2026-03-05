import LeanSharp.StochasticSam
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic

/-!
# Stochastic ZSharp Convergence Bound

We formalize the stochastic convergence of the ZSharp algorithm.
Unlike the deterministic case, we must account for the variance of the
stochastic gradient and its interaction with the Z-score filter.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {d : ℕ} [Fact (0 < d)]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

-- The loss function and its global minimum.
variable (L : W d → ℝ) (w_star : W d)

/-- The Stochastic Alignment Condition:
    Generalizes the deterministic alignment condition to the stochastic case.
    The filtered stochastic gradient must, on average, provide sufficient descent. -/
def stochastic_alignment_condition (w : W d) (η z μ : ℝ) (g_adv : Ω → W d) : Prop :=
  let g_f (ω : Ω) := filtered_gradient (g_adv ω) z
  Integrable (fun ω => ‖g_f ω‖^2) ℙ ∧
  2 * η * (@inner ℝ _ _ (𝔼[fun ω => g_f ω]) (w - w_star)) -
  η^2 * 𝔼[fun ω => ‖g_f ω‖^2] ≥ η * μ * ‖w - w_star‖^2

/-- **Stochastic ZSharp Convergence Theorem**:
    Under the stochastic alignment condition and standard optimization assumptions,
    the parameter distance to the optimum decreases in expectation. -/
theorem stochastic_zsharp_convergence {g_adv : Ω → W d} (w : W d) (η ρ z σsq μ : ℝ)
    (h_sgd : is_stochastic_gradient L g_adv (w + sam_perturbation L w ρ))
    (h_var : has_bounded_variance L g_adv (w + sam_perturbation L w ρ) σsq)
    (h_align : stochastic_alignment_condition w_star w η z μ g_adv) :
    𝔼[fun ω => ‖stochastic_zsharp_step w η z g_adv ω - w_star‖^2] ≤
      (1 - η * μ) * ‖w - w_star‖^2 := by
  -- The proof will use linearity of expectation and the stochastic alignment condition.
  unfold stochastic_zsharp_step
  -- ‖(w - η • g_f ω) - w_star‖^2 = ‖(w - w_star) - η • g_f ω‖^2
  have hrw : ∀ ω, (w - η • filtered_gradient (g_adv ω) z) - w_star =
                  (w - w_star) - η • filtered_gradient (g_adv ω) z := by intro ω; abel
  simp_rw [hrw, norm_sub_sq_real, inner_smul_right, real_inner_comm]
  -- Linearity of expectation: 𝔼[‖A - B‖^2] = ‖A‖^2 - 2⟨A, 𝔼[B]⟩ + 𝔼[‖B‖^2]
  -- Note: w and w_star are deterministic with respect to the noise ω.
  admit

end LeanSharp
