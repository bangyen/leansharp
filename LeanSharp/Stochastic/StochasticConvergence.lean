/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.StochasticSam
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Stochastic ZSharp Convergence Bound

This module formalizes the stochastic convergence theory for the ZSharp algorithm.
It accounts for the variance in stochastic gradients and its interaction with
the Z-score filter.

## Main definitions

* `stochastic_alignment_condition`: Generalization of the alignment condition
  to the expectation of the filtered stochastic gradient.

## Main theorems

* `stochastic_zsharp_convergence`: Proves that the expected squared distance to
  the optimum decreases in each step.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {d : ℕ}
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Stochastic Alignment Condition**: A generalization of the alignment condition
to the stochastic setting. It requires that the filtered stochastic gradient
provide sufficient descent in expectation. -/
def stochastic_alignment_condition (w_star w : W d) (η z μ : ℝ) (g_adv : Ω → W d) : Prop :=
  let g_f (ω : Ω) := filtered_gradient (g_adv ω) z
  Integrable g_f ∧
  Integrable (fun ω => ‖g_f ω‖^2) ∧
  2 * η * (@inner ℝ _ _ (𝔼[g_f]) (w - w_star)) -
  η^2 * 𝔼[fun ω => ‖g_f ω‖^2] ≥ η * μ * ‖w - w_star‖^2

/-- **Stochastic ZSharp Convergence Theorem**: Under the stochastic alignment
condition and standard assumptions, the distance to the optimum decreases in
expectation. -/
theorem stochastic_zsharp_convergence (w_star : W d) {g_adv : Ω → W d} (w : W d)
    (η z μ : ℝ)
    (h_align : stochastic_alignment_condition w_star w η z μ g_adv) :
    𝔼[fun ω => ‖stochastic_zsharp_step w η z g_adv ω - w_star‖^2] ≤
      (1 - η * μ) * ‖w - w_star‖^2 := by
  let A : W d := w - w_star
  let B (ω : Ω) : W d := filtered_gradient (g_adv ω) z
  have hrw : ∀ ω, stochastic_zsharp_step w η z g_adv ω - w_star = A - η • B ω := by
    intro ω; unfold stochastic_zsharp_step A B
    simp only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  -- Step 1: Expand the squared distance using the helper lemma
  have h_body : (fun ω => ‖stochastic_zsharp_step w η z g_adv ω - w_star‖^2) =
                (fun ω => ‖A‖^2 - 2 * η * inner ℝ (B ω) A + η^2 * ‖B ω‖^2) := by
    funext ω
    rw [hrw, norm_sub_smul_sq A (B ω) η]
  rw [h_body]
  -- Step 2: Verify integrability of the expansion terms to apply linearity of expectation
  have h_int_B2 : Integrable (fun ω => ‖B ω‖^2) := h_align.2.1
  have h_itg_eta_B2 : Integrable (fun ω => η^2 * ‖B ω‖^2) :=
    Integrable.const_mul h_int_B2 (η^2)
  have h_int_inner : Integrable (fun ω => 2 * η * inner ℝ (B ω) A) :=
    Integrable.const_mul (h_align.1.inner_const A) _
  have h_int_A2 : Integrable (fun _ : Ω => ‖A‖^2) := integrable_const (‖A‖^2)
  -- Step 3: Use linearity of expectation and the stochastic alignment condition
  calc (∫ ω, ‖A‖^2 - 2 * η * inner ℝ (B ω) A + η^2 * ‖B ω‖^2 ∂volume)
      -- Distribute the integral over the sum
      _ = (∫ ω, ‖A‖^2 - 2 * η * inner ℝ (B ω) A ∂volume) +
          (∫ ω, η^2 * ‖B ω‖^2 ∂volume) := by
          apply integral_add
          · apply Integrable.sub h_int_A2 h_int_inner
          · exact h_itg_eta_B2
      _ = (∫ ω, ‖A‖^2 ∂volume) - (∫ ω, 2 * η * inner ℝ (B ω) A ∂volume) +
          (∫ ω, η^2 * ‖B ω‖^2 ∂volume) := by
          rw [integral_sub h_int_A2 h_int_inner]
      -- Pull out constants from the integrals
      _ = ‖A‖^2 - 2 * η * (∫ ω, inner ℝ (B ω) A ∂volume) +
          η^2 * (∫ ω, ‖B ω‖^2 ∂volume) := by
          rw [integral_const, probReal_univ, one_smul]
          have h1 : (∫ ω, 2 * η * inner ℝ (B ω) A ∂volume) =
                    2 * η * (∫ ω, inner ℝ (B ω) A ∂volume) :=
            integral_const_mul (2 * η) (fun ω => inner ℝ (B ω) A)
          have h2 : (∫ ω, η^2 * ‖B ω‖^2 ∂volume) = η^2 * (∫ ω, ‖B ω‖^2 ∂volume) :=
            integral_const_mul (η^2) (fun ω => ‖B ω‖^2)
          rw [h1, h2]
      -- Move the inner product through the integral
      _ = ‖A‖^2 - 2 * η * inner ℝ (∫ ω, B ω ∂volume) A +
          η^2 * (∫ ω, ‖B ω‖^2 ∂volume) := by
          have h_int : (∫ ω, inner ℝ (B ω) A ∂volume) = inner ℝ (∫ ω, B ω ∂volume) A := by
            have h_comm : (fun ω => inner ℝ (B ω) A) = (fun ω => inner ℝ A (B ω)) := by
              funext ω; rw [real_inner_comm]
            rw [congr_arg (integral volume) h_comm, integral_inner h_align.1 A,
                real_inner_comm]
          rw [h_int]
      _ = ‖A‖^2 - (2 * η * inner ℝ (∫ ω, B ω ∂volume) A -
          η^2 * (∫ ω, ‖B ω‖^2 ∂volume)) := by
          ring
      -- Apply the descent condition from stochastic_alignment_condition
      _ ≤ ‖A‖^2 - (η * μ * ‖A‖^2) := by
          apply sub_le_sub_left
          exact h_align.2.2
      _ = (1 - η * μ) * ‖w - w_star‖^2 := by unfold A; ring

end LeanSharp
