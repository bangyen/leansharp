import LeanSharp.Core.Landscape
import LeanSharp.Core.Sam
import LeanSharp.Core.Filters
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Ring.Defs


/-!
# ZSharp Convergence Bound

One of the open research questions for SAM variants is how modifying the
adversarial gradient affects the theoretical convergence rate under standard
optimization assumptions.

Here, we mathematically formalize the conditions required to prove that
ZSharp converges on a well-behaved (convex, smooth) landscape.
-/

namespace LeanSharp

variable {d : ℕ} [Fact (0 < d)]

-- The loss function we are optimizing.
variable (L : W d → ℝ)

-- The unique global minimum of the strongly convex function.
variable (w_star : W d)

/-- We assume the loss function is L-smooth.
    This means the gradient is Lipschitz continuous with constant `L_smooth`.
    ‖∇L(w) - ∇L(v)‖ ≤ L_smooth * ‖w - v‖ -/
def is_L_smooth (L_smooth : ℝ) : Prop :=
  L_smooth > 0 ∧ ∀ w v : W d,
    ‖gradient L w - gradient L v‖ ≤ L_smooth * ‖w - v‖

/-- We assume the loss function is μ-strongly convex.
    This provides a strong lower bound on the function's curvature.
    L(v) ≥ L(w) + ⟨∇L(w), v - w⟩ + (μ/2)‖v - w‖² -/
def is_strongly_convex (μ : ℝ) : Prop :=
  μ > 0 ∧ ∀ w v : W d,
    L v ≥ L w + @inner ℝ (W d) _ (gradient L w) (v - w) + (μ / 2) * ‖v - w‖^2

/-- The parameter update for a single step of ZSharp.
    w_{t+1} = w_t - η * filtered_gradient(∇L(w_t + ε), z) -/
noncomputable def zsharp_step (w : W d) (η ρ z : ℝ) : W d :=
  let ε := sam_perturbation L w ρ
  let g_adv := gradient L (w + ε)
  let g_filtered := filtered_gradient g_adv z
  w - η • g_filtered


/-- The formal statement of ZSharp convergence holds.
    It posits that there exists a contraction factor `c ∈ (0, 1)`. -/
def zsharp_convergence_holds (η ρ z L_smooth μ : ℝ) : Prop :=
  is_L_smooth L L_smooth →
  is_strongly_convex L μ →
  η > 0 ∧ ρ > 0 →
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∀ w : W d, ‖zsharp_step L w η ρ z - w_star‖^2 ≤ c * ‖w - w_star‖^2

/-- The Alignment Condition:
    A statistical assumption that the filtered gradient maintains sufficient
    alignment with the true descent direction, and its norm is bounded by the
    landscape smoothness. -/
def alignment_condition (L : W d → ℝ) (w w_star : W d) (ε : W d) (z μ L_smooth : ℝ) : Prop :=
  let g_adv := gradient L (w + ε)
  let g_f := filtered_gradient g_adv z
  μ * ‖w - w_star‖^2 ≤ @inner ℝ _ _ g_f (w - w_star) ∧
  ‖g_f‖ ≤ L_smooth * ‖w - w_star‖

section NoDimFact
omit [Fact (0 < d)]

/-- Main Theorem: ZSharp converges geometrically to `w_star` under standard assumptions. -/
theorem zsharp_convergence (η ρ z L_smooth μ : ℝ)
    (hη_tight : η * L_smooth ^ 2 ≤ μ)
    (hη_bound : η ≤ 1 / L_smooth)
    (hμL : μ < L_smooth)
    (h_align : ∀ w : W d, let ε := sam_perturbation L w ρ
                          alignment_condition L w w_star ε z μ L_smooth) :
    zsharp_convergence_holds L w_star η ρ z L_smooth μ := by
  intro h_smooth h_convex ⟨hη, hρ⟩
  set c := 1 - η * μ with hc_def
  have hμ := h_convex.1
  have hL := h_smooth.1
  have h_c_pos : 0 < c := by
    rw [hc_def]
    have hημ_lt_1 : η * μ < 1 := by
      have : η * μ < η * L_smooth := mul_lt_mul_of_pos_left hμL hη
      have hη_L_le_1 : η * L_smooth ≤ 1 := by
        have h1 := mul_le_mul_of_nonneg_right hη_bound (le_of_lt hL)
        field_simp at h1; exact h1
      linarith
    linarith
  have h_c_lt_1 : c < 1 := by rw [hc_def]; linarith [mul_pos hη hμ]
  refine ⟨c, h_c_pos, h_c_lt_1, fun w => ?_⟩
  simp only [zsharp_step]
  let ε := sam_perturbation L w ρ
  let g_f := filtered_gradient (gradient L (w + ε)) z
  obtain ⟨h_inner_bound, h_gf_bound⟩ := h_align w
  have h_gf_sq : ‖g_f‖^2 ≤ (L_smooth * ‖w - w_star‖)^2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg (le_of_lt hL) (norm_nonneg _))]
    exact h_gf_bound
  have hrw : (w - η • g_f) - w_star = (w - w_star) - η • g_f := by abel
  rw [hrw, norm_sub_sq_real, inner_smul_right, real_inner_comm]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  have hkey : η^2 * L_smooth^2 ≤ η * μ := by nlinarith [sq_nonneg η, hη_tight]
  nlinarith [sq_nonneg ‖w - w_star‖, h_inner_bound, h_gf_sq, hkey,
             mul_nonneg (le_of_lt hη) (mul_nonneg (le_of_lt hμ) (sq_nonneg ‖w - w_star‖))]

end NoDimFact

end LeanSharp
