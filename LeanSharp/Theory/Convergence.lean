/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import LeanSharp.Core.Sam
import LeanSharp.Core.Filters
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic

/-!
# ZSharp Convergence Bound

This module formalizes the geometric convergence of the ZSharp algorithm
under standard optimization assumptions (L-smoothness and strong convexity).
It also defines conditions for stochastic non-convex convergence.

## Main definitions

* `is_L_smooth`: Predicate for $L$-smoothness of a function.
* `is_strongly_convex`: Predicate for $\mu$-strong convexity of a function.
* `zsharp_step`: The single-step update rule for the Z-score filtered SAM.
* `alignment_condition`: An assumption about the alignment of the filtered gradient.
* `stochastic_descent_condition`: A condition for non-convex convergence.

## Main theorems

* `zsharp_convergence`: Proves that ZSharp converges geometrically to the
  optimum given sufficient alignment and small step sizes.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {d : ℕ} [Fact (0 < d)]

/-- A function $L$ is $L_{smooth}$-smooth if its gradient is Lipschitz continuous
with constant $L_{smooth}$. -/
def is_L_smooth (L : W d → ℝ) (L_smooth : ℝ) : Prop :=
  L_smooth > 0 ∧ ∀ w v : W d,
    ‖gradient L w - gradient L v‖ ≤ L_smooth * ‖w - v‖

/-- A function $L$ is $\mu$-strongly convex if it is bounded below by a quadratic. -/
def is_strongly_convex (L : W d → ℝ) (μ : ℝ) : Prop :=
  μ > 0 ∧ ∀ w v : W d,
    L v ≥ L w + @inner ℝ (W d) _ (gradient L w) (v - w) + (μ / 2) * ‖v - w‖^2

/-- The parameter update for a single step of ZSharp.
`w_{t+1} = w_t - η * filtered_gradient(∇L(w_t + ε), z)` -/
noncomputable def zsharp_step (L : W d → ℝ) (w : W d) (η ρ z : ℝ) : W d :=
  let ε := sam_perturbation L w ρ
  let g_adv := gradient L (w + ε)
  let g_filtered := filtered_gradient g_adv z
  w - η • g_filtered

/-- The property that ZSharp converges geometrically to a target point `w_star`. -/
def zsharp_convergence_holds (L : W d → ℝ) (w_star : W d) (η ρ z L_smooth μ : ℝ) : Prop :=
  is_L_smooth L L_smooth →
  is_strongly_convex L μ →
  η > 0 ∧ ρ > 0 →
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∀ w : W d, ‖zsharp_step L w η ρ z - w_star‖^2 ≤ c * ‖w - w_star‖^2

/-- **Alignment Condition**: A statistical assumption that the filtered gradient
maintains sufficient alignment with the true descent direction. -/
def alignment_condition (L : W d → ℝ) (w w_star : W d) (ε : W d) (z μ L_smooth : ℝ) : Prop :=
  let g_adv := gradient L (w + ε)
  let g_f := filtered_gradient g_adv z
  μ * ‖w - w_star‖^2 ≤ @inner ℝ _ _ g_f (w - w_star) ∧
  ‖g_f‖ ≤ L_smooth * ‖w - w_star‖

/-- **Stochastic Descent Condition**: A condition for smooth non-convex functions
requiring that the filtered stochastic gradient provide sufficient descent
relative to the expected gradient norm and variance. -/
def stochastic_descent_condition {Ω : Type*} [MeasureSpace Ω]
    (L : W d → ℝ) (η z L_smooth σsq : ℝ) (g_adv : Ω → W d) (w : W d) : Prop :=
  let g_f (ω : Ω) := filtered_gradient (g_adv ω) z
  let gradL := gradient L w
  Integrable g_f ∧
  Integrable (fun ω => ‖g_f ω‖^2) ∧
  𝔼[fun ω => inner ℝ (g_f ω) (gradient L w)] - (η * L_smooth / 2) * 𝔼[fun ω => ‖g_f ω‖^2] ≥
    (1 / 2) * ‖gradient L w‖^2 - (η * L_smooth / 2) * σsq

section NoDimFact
omit [Fact (0 < d)]

/-- **Main Theorem**: ZSharp converges geometrically to `w_star` under smoothness,
strong convexity, and the alignment condition. -/
theorem zsharp_convergence (L : W d → ℝ) (w_star : W d) (η ρ z L_smooth μ : ℝ)
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
