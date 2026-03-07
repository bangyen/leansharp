/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Sam
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
  Integrable (fun ω => ‖g_f ω‖ ^ 2) ∧
  2 * η * (@inner ℝ _ _ (𝔼[g_f]) (w - w_star)) -
  η^2 * 𝔼[fun ω => ‖g_f ω‖ ^ 2] ≥ η * μ * ‖w - w_star‖ ^ 2

/-- **Stochastic ZSharp Convergence Theorem**: Under the stochastic alignment
condition and standard assumptions, the distance to the optimum decreases in
expectation. -/
theorem stochastic_zsharp_convergence (w_star : W d) {g_adv : Ω → W d} (w : W d)
    (η z μ : ℝ)
    (h_align : stochastic_alignment_condition w_star w η z μ g_adv) :
    𝔼[fun ω => ‖stochastic_zsharp_step w η z g_adv ω - w_star‖ ^ 2] ≤
      (1 - η * μ) * ‖w - w_star‖ ^ 2 := by
  let A : W d := w - w_star
  let B (ω : Ω) : W d := filtered_gradient (g_adv ω) z
  have hrw : ∀ ω, stochastic_zsharp_step w η z g_adv ω - w_star = A - η • B ω := by
    intro ω; unfold stochastic_zsharp_step A B
    simp only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  -- Step 1: Expand the squared distance using the helper lemma
  have h_expansion := stochastic_dist_expansion A B η h_align.1 h_align.2.1
  simp_rw [hrw]
  rw [h_expansion]
  -- Step 2: Apply the stochastic alignment condition and algebra reduction
  have h_bound : 2 * η * inner ℝ 𝔼[B] A - η^2 * 𝔼[fun ω => ‖B ω‖^2] ≥ η * μ * ‖A‖^2 :=
    h_align.2.2
  linarith [pow_two_nonneg ‖A‖]

end LeanSharp
