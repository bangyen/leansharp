/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import LeanSharp.Core.Objective
import LeanSharp.Core.Taylor.SamBounds
import LeanSharp.Theory.Dynamics.Schedulers
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Notation

/-!
# ZSharp Convergence Bound

This module formalizes the geometric convergence of the ZSharp algorithm
under standard optimization assumptions (L-smoothness and strong convexity).
It also defines conditions for stochastic non-convex convergence.

## Main definitions

* `IsLSmooth`: Predicate for $L$-smoothness of a function.
* `IsStronglyConvex`: Predicate for $\mu$-strong convexity of a function.
* `zsharpStep`: The single-step update rule for the Z-score filtered SAM.
* `AlignmentCondition`: An assumption about the alignment of the filtered gradient.

## Main theorems

* `zsharp_convergence`: Proves that ZSharp converges geometrically to the
  optimum given sufficient alignment and small step sizes.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- A function $L$ is $L_{smooth}$-smooth if its gradient is Lipschitz continuous
with constant $L_{smooth}$. Predicate for a function being L-smooth. -/
def IsLSmooth (L : W ι → ℝ) (L_smooth : ℝ) : Prop :=
  L_smooth > 0 ∧ ∀ w v : W ι,
    ‖gradient L w - gradient L v‖ ≤ L_smooth * ‖w - v‖

/-- Predicate for a function being μ-strongly convex. -/
def IsStronglyConvex (L : W ι → ℝ) (μ : ℝ) : Prop :=
  μ > 0 ∧ ∀ w v : W ι,
    L v ≥ L w + @inner ℝ (W ι) _ (gradient L w) (v - w) + (μ / 2) * ‖v - w‖^2

/-- A structure bundling a smooth objective with strong convexity. -/
structure StronglyConvexObjective (ι : Type*) [Fintype ι] extends SmoothObjective ι where

  /-- The strong convexity constant. -/
  μ : ℝ

  /-- Proof that the loss is μ-strongly convex. -/
  strongly_convex : IsStronglyConvex toFun μ

/-- The parameter update for a single step of ZSharp with a learning rate schedule.
`w_{t+1} = w_t - η_t * filteredGradient(∇L(w_t + ε), z)` -/
noncomputable def zsharpStep (L : W ι → ℝ) (w : W ι) (η : ℕ → ℝ) (t : ℕ)
    (ρ z : ℝ) : W ι :=
  let ε := samPerturbation L w ρ
  let g_adv := gradient L (w + ε)
  let g_filtered := filteredGradient g_adv z
  w - (η t) • g_filtered

/-- The property that ZSharp converges geometrically to a target point `w_star`
under a learning rate schedule. -/
def ZSharpConvergenceHolds (L : W ι → ℝ) (w_star : W ι) (η : ℕ → ℝ)
    (ρ z L_smooth μ : ℝ) : Prop :=
  IsLSmooth L L_smooth →
  IsStronglyConvex L μ →
  (∀ t, η t > 0) ∧ ρ > 0 →
  ∃ c : ℕ → ℝ, (∀ t, 0 < c t ∧ c t < 1) ∧
    ∀ w : W ι, ∀ t : ℕ,
      ‖zsharpStep L w η t ρ z - w_star‖^2 ≤ c t * ‖w - w_star‖^2

/-- **Alignment Condition**: A statistical assumption that the filtered gradient
maintains sufficient alignment with the true descent direction. -/
def AlignmentCondition (L : W ι → ℝ) (w w_star : W ι) (ε : W ι)
    (z μ L_smooth : ℝ) : Prop :=
  let g_adv := gradient L (w + ε)
  let g_f := filteredGradient g_adv z
  μ * ‖w - w_star‖^2 ≤ @inner ℝ _ _ g_f (w - w_star) ∧
  ‖g_f‖ ≤ L_smooth * ‖w - w_star‖

/-- A structure bundling the full set of assumptions for ZSharp convergence. -/
structure ZSharpModel (ι : Type*) [Fintype ι] where

  /-- The strongly convex and smooth objective. -/
  L : StronglyConvexObjective ι

  /-- The global optimum point. -/
  w_star : W ι

  /-- The SAM perturbation radius. -/
  ρ : ℝ

  /-- The Z-score filter threshold. -/
  z : ℝ

  /-- The foundational alignment condition connecting geometry to filtering. -/
  alignment : ∀ w : W ι,
    let ε := samPerturbation L.toFun w ρ
    AlignmentCondition L.toFun w w_star ε z L.μ (L.smoothness : ℝ)

/-- **ZSharp Convergence Theorem**: Under the bundled ZSharp assumptions, any learning
rate schedule satisfying the local 'tightness' condition (step size scaled by
smoothness is bounded by strong convexity) guarantees convergence to the optimum. -/
theorem zsharp_convergence (M : ZSharpModel ι) (η : Schedule)
    (hη_tight : ∀ t, η t * (M.L.smoothness : ℝ) ^ 2 ≤ M.L.μ)
    (hμL : M.L.μ < (M.L.smoothness : ℝ)) :
    ZSharpConvergenceHolds M.L.toFun M.w_star η M.ρ M.z (M.L.smoothness : ℝ) M.L.μ := by
  let L_obj := M.L
  let w_star := M.w_star
  let ρ := M.ρ
  let z := M.z
  let h_align := M.alignment
  intro hL_smooth_packed hμ_convex_packed ⟨hη, hρ⟩
  -- Step 1: Define the sequence of contraction factors c_t = 1 - η_t * μ
  let c (t : ℕ) := 1 - η t * L_obj.μ
  have h_c_valid : ∀ t, 0 < c t ∧ c t < 1 := by
    intro t
    constructor
    · have hη_nonneg : 0 ≤ η t := (le_of_lt (hη t))
      have hLsq_pos : 0 < (L_obj.smoothness : ℝ) ^ 2 := by
        have hL_pos : 0 < (L_obj.smoothness : ℝ) := by
          have hμ_pos : 0 < L_obj.μ := L_obj.strongly_convex.1
          linarith [hμL, hμ_pos]
        positivity
      have hη_le : η t ≤ L_obj.μ / ((L_obj.smoothness : ℝ) ^ 2) := by
        rw [le_div_iff₀ hLsq_pos]
        exact hη_tight t
      have hμ_nonneg : 0 ≤ L_obj.μ := L_obj.strongly_convex.1.le
      have h_eta_mul_mu_le :
          η t * L_obj.μ ≤ (L_obj.μ / ((L_obj.smoothness : ℝ) ^ 2)) * L_obj.μ :=
        mul_le_mul_of_nonneg_right hη_le hμ_nonneg
      have h_mu_ratio_lt_one : (L_obj.μ / ((L_obj.smoothness : ℝ) ^ 2)) * L_obj.μ < 1 := by
        have hL_pos : 0 < (L_obj.smoothness : ℝ) := by
          have hμ_pos : 0 < L_obj.μ := L_obj.strongly_convex.1
          linarith [hμL, hμ_pos]
        have hμ_sq_lt_L_sq : L_obj.μ ^ 2 < (L_obj.smoothness : ℝ) ^ 2 := by
          have hμ_abs_lt_L : |L_obj.μ| < (L_obj.smoothness : ℝ) := by
            have hμ_pos : 0 < L_obj.μ := L_obj.strongly_convex.1
            rw [abs_of_pos hμ_pos]
            exact hμL
          have hL_pos : 0 < (L_obj.smoothness : ℝ) := by linarith
          nlinarith [hμ_abs_lt_L, hL_pos]
        have hdiv : L_obj.μ / ((L_obj.smoothness : ℝ) ^ 2) * L_obj.μ =
            L_obj.μ ^ 2 / ((L_obj.smoothness : ℝ) ^ 2) := by
          field_simp [hL_pos.ne']
        rw [hdiv]
        exact (div_lt_one (pow_pos hL_pos 2)).2 hμ_sq_lt_L_sq
      exact sub_pos.mpr (lt_of_le_of_lt h_eta_mul_mu_le h_mu_ratio_lt_one)
    · exact sub_lt_self 1 (mul_pos (hη t) L_obj.strongly_convex.1)
  refine ⟨c, h_c_valid, fun w t => ?_⟩
  rw [zsharpStep]
  let ε := samPerturbation L_obj.toFun w ρ
  let g_f := filteredGradient (gradient L_obj.toFun (w + ε)) z
  -- Step 2: Bound the filtered gradient norm squared using the alignment condition
  obtain ⟨h_inner_bound, h_gf_bound⟩ := h_align w
  have h_gf_sq : ‖g_f‖^2 ≤ ((L_obj.smoothness : ℝ) * ‖w - w_star‖)^2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg L_obj.smoothness) (norm_nonneg _))]
    exact h_gf_bound
  -- Step 3: Rearrange the quadratic expansion of the update step (inlined)
  rw [norm_descent_step_sq w w_star g_f (η t)]
  have h_eta_pos : 0 < η t := hη t
  have hkey : (η t) ^ 2 * (L_obj.smoothness : ℝ) ^ 2 ≤ (η t) * L_obj.μ := by
    rw [sq, mul_assoc]
    apply mul_le_mul_of_nonneg_left (hη_tight t) h_eta_pos.le
  have h_main :
      ‖w - w_star‖ ^ 2 - 2 * η t * inner ℝ g_f (w - w_star) + η t ^ 2 * ‖g_f‖ ^ 2 ≤
        (1 - η t * L_obj.μ) * ‖w - w_star‖ ^ 2 := by
    calc ‖w - w_star‖ ^ 2 - 2 * η t * inner ℝ g_f (w - w_star) + η t ^ 2 * ‖g_f‖ ^ 2
      _ ≤ ‖w - w_star‖ ^ 2 - 2 * η t * (L_obj.μ * ‖w - w_star‖ ^ 2) +
          η t ^ 2 * ((L_obj.smoothness : ℝ) * ‖w - w_star‖) ^ 2 := by
        nlinarith [h_inner_bound, h_gf_sq, h_eta_pos]
      _ = (1 - 2 * η t * L_obj.μ + η t ^ 2 * (L_obj.smoothness : ℝ) ^ 2) *
          ‖w - w_star‖ ^ 2 := by
        rw [sq]; ring
      _ ≤ (1 - η t * L_obj.μ) * ‖w - w_star‖ ^ 2 := by
        nlinarith [hkey, sq_nonneg ‖w - w_star‖]
  exact h_main

end LeanSharp
