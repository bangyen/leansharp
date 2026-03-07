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
  Integrable (fun ω => ‖g_f ω‖ ^ 2) ∧
  2 * η * (@inner ℝ _ _ (𝔼[g_f]) (w - w_star)) -
  η^2 * 𝔼[fun ω => ‖g_f ω‖ ^ 2] ≥ η * μ * ‖w - w_star‖ ^ 2

/-- **Integral Inner Product Identity**: The integral of an inner product with a
constant vector is the inner product of the integral. -/
lemma integral_inner_const {Ω : Type*} [MeasureSpace Ω]
    {f : Ω → W d} (hf : Integrable f) (c : W d) :
    (∫ ω, inner ℝ (f ω) c ∂volume) = inner ℝ (∫ ω, f ω ∂volume) c := by
  have : (fun ω => inner ℝ (f ω) c) = (fun ω => inner ℝ c (f ω)) :=
    by funext ω; rw [real_inner_comm]
  rw [this, integral_inner hf c, real_inner_comm]

/-- **Stochastic Distance Expansion**: The identity for the expected squared distance
after an update step: $𝔼[‖A - η • B‖ ^ 2] = ‖A‖ ^ 2 - 2η⟨𝔼[B], A⟩ +$
$η ^ 2 𝔼[‖B‖ ^ 2]$.
-/
lemma stochastic_dist_expansion (A : W d) (B : Ω → W d) (η : ℝ)
    (h_int_B : Integrable B) (h_int_B2 : Integrable (fun ω => ‖B ω‖ ^ 2)) :
    𝔼[fun ω => ‖A - η • B ω‖ ^ 2] =
      ‖A‖ ^ 2 - 2 * η * inner ℝ (𝔼[B]) A + η^2 * 𝔼[fun ω => ‖B ω‖ ^ 2] := by
  have h_int_A2 : Integrable (fun _ : Ω => ‖A‖ ^ 2) := integrable_const (‖A‖ ^ 2)
  have h_int_inner : Integrable (fun ω => inner ℝ (B ω) A) := h_int_B.inner_const A
  have h_int_2ηB : Integrable (fun ω => 2 * η * inner ℝ (B ω) A) :=
    Integrable.const_mul h_int_inner (2 * η)
  have h_int_η2B2 : Integrable (fun ω => η^2 * ‖B ω‖ ^ 2) :=
    Integrable.const_mul h_int_B2 (η^2)
  have h_int_sub : Integrable (fun ω => ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A) :=
    h_int_A2.sub h_int_2ηB
  calc 𝔼[fun ω => ‖A - η • B ω‖ ^ 2]
    _ = 𝔼[fun ω => ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A + η^2 * ‖B ω‖ ^ 2] := by
        simp_rw [norm_sub_smul_sq]
    _ = 𝔼[fun ω => ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A] +
        𝔼[fun ω => η^2 * ‖B ω‖ ^ 2] :=
        integral_add h_int_sub h_int_η2B2
    _ = 𝔼[fun _ => ‖A‖ ^ 2] - 𝔼[fun ω => 2 * η * inner ℝ (B ω) A] +
        𝔼[fun ω => η ^ 2 * ‖B ω‖ ^ 2] := by
        rw [integral_sub h_int_A2 h_int_2ηB]
    _ = ‖A‖ ^ 2 - 2 * η * 𝔼[fun ω => inner ℝ (B ω) A] +
        η ^ 2 * 𝔼[fun ω => ‖B ω‖ ^ 2] := by
        rw [integral_const, probReal_univ, one_smul,
          integral_const_mul, integral_const_mul]
    _ = ‖A‖ ^ 2 - 2 * η * inner ℝ (𝔼[B]) A +
        η ^ 2 * 𝔼[fun ω => ‖B ω‖ ^ 2] := by
        rw [integral_inner_const h_int_B A]

/-- **Alignment Algebra Reduction**: Auxiliary lemma for the stochastic convergence.
Concludes (1 - ημ) · ‖A‖² from the alignment bound. -/
lemma alignment_algebra_reduction (A : W d) (η μ : ℝ) (bound : ℝ)
    (h_align : bound ≥ η * μ * ‖A‖ ^ 2) :
    ‖A‖ ^ 2 - bound ≤ (1 - η * μ) * ‖A‖ ^ 2 :=
  by linarith [pow_two_nonneg ‖A‖]

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
  -- Step 2: Apply the stochastic alignment condition
  have h_bound : 2 * η * inner ℝ 𝔼[B] A - η^2 * 𝔼[fun ω => ‖B ω‖^2] ≥ η * μ * ‖A‖^2 :=
    h_align.2.2
  -- Step 3: Use the algebra reduction helper
  calc ‖A‖^2 - 2 * η * inner ℝ 𝔼[B] A + η^2 * 𝔼[fun ω => ‖B ω‖^2]
      _ = ‖A‖ ^ 2 - (2 * η * inner ℝ 𝔼[B] A -
          η ^ 2 * 𝔼[fun ω => ‖B ω‖ ^ 2]) := by ring
      _ ≤ (1 - η * μ) * ‖w - w_star‖^2 := by
          apply alignment_algebra_reduction A η μ
          exact h_bound

end LeanSharp
