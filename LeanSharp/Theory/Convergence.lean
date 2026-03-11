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

## Main theorems

* `zsharp_convergence`: Proves that ZSharp converges geometrically to the
  optimum given sufficient alignment and small step sizes.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- A function $L$ is $L_{smooth}$-smooth if its gradient is Lipschitz continuous
with constant $L_{smooth}$. -/
def is_L_smooth (L : W ι → ℝ) (L_smooth : ℝ) : Prop :=
  L_smooth > 0 ∧ ∀ w v : W ι,
    ‖gradient L w - gradient L v‖ ≤ L_smooth * ‖w - v‖

/-- A function $L$ is $\mu$-strongly convex if it is bounded below by a quadratic. -/
def is_strongly_convex (L : W ι → ℝ) (μ : ℝ) : Prop :=
  μ > 0 ∧ ∀ w v : W ι,
    L v ≥ L w + @inner ℝ (W ι) _ (gradient L w) (v - w) + (μ / 2) * ‖v - w‖^2

/-- The parameter update for a single step of ZSharp.
`w_{t+1} = w_t - η * filtered_gradient(∇L(w_t + ε), z)` -/
noncomputable def zsharp_step (L : W ι → ℝ) (w : W ι) (η ρ z : ℝ) : W ι :=
  let ε := sam_perturbation L w ρ
  let g_adv := gradient L (w + ε)
  let g_filtered := filtered_gradient g_adv z
  w - η • g_filtered

/-- The property that ZSharp converges geometrically to a target point `w_star`. -/
def zsharp_convergence_holds (L : W ι → ℝ) (w_star : W ι) (η ρ z L_smooth μ : ℝ) : Prop :=
  is_L_smooth L L_smooth →
  is_strongly_convex L μ →
  η > 0 ∧ ρ > 0 →
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∀ w : W ι, ‖zsharp_step L w η ρ z - w_star‖^2 ≤ c * ‖w - w_star‖^2

/-- **Alignment Condition**: A statistical assumption that the filtered gradient
maintains sufficient alignment with the true descent direction. -/
def alignment_condition (L : W ι → ℝ) (w w_star : W ι) (ε : W ι) (z μ L_smooth : ℝ) : Prop :=
  let g_adv := gradient L (w + ε)
  let g_f := filtered_gradient g_adv z
  μ * ‖w - w_star‖^2 ≤ @inner ℝ _ _ g_f (w - w_star) ∧
  ‖g_f‖ ≤ L_smooth * ‖w - w_star‖

/-- **Main Theorem**: ZSharp converges geometrically to `w_star` under smoothness,
strong convexity, and the alignment condition. -/
theorem zsharp_convergence (L : W ι → ℝ) (w_star : W ι) (η ρ z L_smooth μ : ℝ)
    (hη_tight : η * L_smooth ^ 2 ≤ μ)
    (hη_bound : η ≤ 1 / L_smooth)
    (hμL : μ < L_smooth)
    (h_align : ∀ w : W ι, let ε := sam_perturbation L w ρ
                          alignment_condition L w w_star ε z μ L_smooth) :
    zsharp_convergence_holds L w_star η ρ z L_smooth μ := by
  intro h_smooth h_convex ⟨hη, hρ⟩
  -- Step 1: Define the contraction factor and verify its properties
  set c := 1 - η * μ with hc_def
  have h_c_valid : 0 < c ∧ c < 1 := by
    constructor
    · have : η * μ < 1 := calc
        η * μ < η * L_smooth := mul_lt_mul_of_pos_left hμL hη
        _     ≤ (1 / L_smooth) * L_smooth := mul_le_mul_of_nonneg_right hη_bound h_smooth.1.le
        _     = 1 := div_mul_cancel₀ 1 h_smooth.1.ne'
      linarith
    · linarith [mul_pos hη h_convex.1]
  obtain ⟨h_c_pos, h_c_lt_1⟩ := h_c_valid
  refine ⟨c, h_c_pos, h_c_lt_1, fun w => ?_⟩
  simp only [zsharp_step]
  let ε := sam_perturbation L w ρ
  let g_f := filtered_gradient (gradient L (w + ε)) z
  -- Step 2: Bound the filtered gradient norm squared using the alignment condition
  obtain ⟨h_inner_bound, h_gf_bound⟩ := h_align w
  have h_gf_sq : ‖g_f‖^2 ≤ (L_smooth * ‖w - w_star‖)^2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (mul_nonneg (le_of_lt h_smooth.1) (norm_nonneg _))]
    exact h_gf_bound
  -- Step 3: Rearrange the quadratic expansion of the update step (inlined)
  rw [norm_descent_step_sq w w_star g_f η]
  have hkey : η ^ 2 * L_smooth ^ 2 ≤ η * μ := by nlinarith [sq_nonneg η, hη_tight]
  nlinarith [sq_nonneg ‖w - w_star‖, h_inner_bound, h_gf_sq, hkey, mul_pow L_smooth ‖w - w_star‖ 2]

end LeanSharp
