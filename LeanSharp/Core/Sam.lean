/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus

open Topology

namespace LeanSharp

variable {ι : Type*} [Fintype ι]

/-- The SAM perturbation neighborhood. We consider all vectors `ε` such that
the L2 norm metric distance `dist 0 ε ≤ ρ`. -/
def perturbation_neighborhood (ρ : ℝ) : Set (W ι) :=
  Metric.closedBall 0 ρ

/-- In SAM, the optimal perturbation `ε*(w)` is the one that maximizes `L(w + ε)`.
To formalize this generically without computing the exact `sup`, we can define
the SAM objective as the supremum over the closed ball. -/
noncomputable def sam_objective (L : W ι → ℝ) (w : W ι) (ρ : ℝ) : ℝ :=
  sSup (L '' ((fun ε => w + ε) '' perturbation_neighborhood ρ))

/-- The first-order SAM perturbation vector. -/
noncomputable def sam_perturbation (L : W ι → ℝ) (w : W ι) (ρ : ℝ) : W ι :=
  let g := gradient L w
  let norm_g := ‖g‖
  if norm_g = 0 then 0 else (ρ / norm_g) • g

/-- **SAM Objective Supremum Property**: The SAM objective at point `w` is always
greater than or equal to the base loss `L w`, provided the neighborhood is
bounded above. -/
theorem sam_objective_ge_self (L : W ι → ℝ) (w : W ι) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h_bdd : BddAbove (L '' ((fun ε => w + ε) '' perturbation_neighborhood ρ))) :
    L w ≤ sam_objective L w ρ := by
  unfold sam_objective perturbation_neighborhood
  refine le_csSup h_bdd ⟨w, ⟨
    0,
    by simp only [Metric.mem_closedBall, dist_self, hρ],
    by simp only [add_zero]
  ⟩, rfl⟩

/-- **SAM Perturbation Differentiability**: The first-order SAM perturbation is
    Fréchet-differentiable at points where the gradient is non-zero and differentiable. -/
theorem has_fderiv_at_sam_perturbation (L : W ι → ℝ) (w : W ι) (ρ : ℝ)
    (h_grad_diff : DifferentiableAt ℝ (gradient L) w)
    (h_nonzero : gradient L w ≠ 0) :
    DifferentiableAt ℝ (fun p => sam_perturbation L p ρ) w := by
  unfold sam_perturbation
  apply DifferentiableAt.congr_of_eventuallyEq
    (f := fun p => (ρ / ‖gradient L p‖) • gradient L p)
  · show DifferentiableAt ℝ (fun p => (ρ / ‖gradient L p‖) • gradient L p) w
    have hc : DifferentiableAt ℝ (fun p => ρ * (‖gradient L p‖)⁻¹) w := by
      apply DifferentiableAt.mul (differentiableAt_const ρ)
      apply DifferentiableAt.inv
      · exact DifferentiableAt.norm (𝕜 := ℝ) h_grad_diff h_nonzero
      · exact norm_ne_zero_iff.mpr h_nonzero
    have hg : DifferentiableAt ℝ
      (fun p => gradient L p) w := h_grad_diff
    exact DifferentiableAt.smul hc hg
  · change (fun p => sam_perturbation L p ρ) =ᶠ[𝓝 w]
      (fun p => (ρ / ‖gradient L p‖) • gradient L p)
    have h_nb := h_grad_diff.continuousAt
      (Metric.ball_mem_nhds (gradient L w)
      (norm_pos_iff.mpr h_nonzero))
    filter_upwards [h_nb] with p hp
    have h_p_nonzero : gradient L p ≠ 0 := by
      intro h_zero
      simp only [
        Set.mem_preimage,
        Metric.mem_ball,
        dist_zero_left,
        h_zero
      ] at hp
      exact (lt_irrefl _) hp
    unfold sam_perturbation
    simp only [h_p_nonzero, norm_eq_zero, ite_false]

end LeanSharp
