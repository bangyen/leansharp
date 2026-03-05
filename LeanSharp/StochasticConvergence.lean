import LeanSharp.StochasticSam
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Stochastic ZSharp Convergence Bound

We formalize the stochastic convergence of the ZSharp algorithm.
Unlike the deterministic case, we must account for the variance of the
stochastic gradient and its interaction with the Z-score filter.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {d : ℕ} [Fact (0 < d)]
variable {Ω : Type*} [MeasureSpace Ω] [hΩ : IsProbabilityMeasure (volume : Measure Ω)]

-- The loss function and its global minimum.
variable (L : W d → ℝ) (w_star : W d)

/-- The Stochastic Alignment Condition:
    Generalizes the deterministic alignment condition to the stochastic case.
    The filtered stochastic gradient must, on average, provide sufficient descent. -/
def stochastic_alignment_condition (w : W d) (η z μ : ℝ) (g_adv : Ω → W d) : Prop :=
  let g_f (ω : Ω) := filtered_gradient (g_adv ω) z
  Integrable g_f ∧
  Integrable (fun ω => ‖g_f ω‖^2) ∧
  2 * η * (@inner ℝ _ _ (𝔼[g_f]) (w - w_star)) -
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
  unfold stochastic_zsharp_step
  let A : W d := w - w_star
  let B (ω : Ω) : W d := filtered_gradient (g_adv ω) z
  -- ‖(w - η • B ω) - w_star‖^2 = ‖A - η • B ω‖^2
  have hrw : ∀ ω, (w - η • B ω) - w_star = A - η • B ω := by
    intro ω
    unfold A
    abel
  simp_rw [hrw, norm_sub_sq_real, inner_smul_right, real_inner_comm]
  -- Linearity of expectation
  have h_int_B2 : Integrable (fun ω => ‖B ω‖^2) := h_align.2.1
  have h_int_inner : Integrable (fun ω => 2 * η * inner ℝ (B ω) A) :=
    Integrable.const_mul (Integrable.inner_left h_align.1) _
  have h_int_A2 : Integrable (fun _ : Ω => ‖A‖^2) := integrable_const (‖A‖^2)
  -- Use calc to resolve the expectation
  calc (∫ ω, ‖A‖^2 - 2 * η * inner ℝ (B ω) A + η^2 * ‖B ω‖^2 ∂volume)
      = (∫ ω, ‖A‖^2 - 2 * η * inner ℝ (B ω) A ∂volume) + (∫ ω, η^2 * ‖B ω‖^2 ∂volume) := by
        apply integral_add
        · apply Integrable.sub h_int_A2 h_int_inner
        · exact Integrable.const_mul h_int_B2 _
    _ = (∫ ω, ‖A‖^2 ∂volume) - (∫ ω, 2 * η * inner ℝ (B ω) A ∂volume) + (∫ ω, η^2 * ‖B ω‖^2 ∂volume) := by
        rw [integral_sub h_int_A2 h_int_inner]
    _ = ‖A‖^2 - 2 * η * (∫ ω, inner ℝ (B ω) A ∂volume) + η^2 * (∫ ω, ‖B ω‖^2 ∂volume) := by
        rw [integral_const, integral_const_mul, integral_const_mul]
        · rw [measure_univ, ENNReal.one_toReal, one_mul]
        · exact h_int_B2
        · exact Integrable.inner_left h_align.1
    _ = ‖A‖^2 - (2 * η * inner ℝ (∫ ω, B ω ∂volume) A - η^2 * (∫ ω, ‖B ω‖^2 ∂volume)) := by
        rw [integral_inner_left h_align.1]; ring
    _ ≤ ‖A‖^2 - (η * μ * ‖A‖^2) := by
        apply sub_le_sub_left
        exact h_align.2.2
    _ = (1 - η * μ) * ‖w - w_star‖^2 := by unfold A; ring

end LeanSharp
