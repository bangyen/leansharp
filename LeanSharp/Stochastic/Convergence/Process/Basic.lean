/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Mechanics.DescentSteps.ZScore
import LeanSharp.Stochastic.Mechanics.SharpnessMap
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Notation

/-!
# Stochastic ZSharp Process - Basic Definitions

This module defines the alignment condition between updates and gradients, and
provides distance expansion lemmas.

## Main Definitions
* `StochasticAlignment`: Condition on gradient-update alignment.

## Main Theorems
* `dist_sq_expansion`: Core identity for expected distance updates.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory NNReal

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Stochastic Alignment Condition**: A generalization of the alignment condition
to the stochastic setting, supporting learning rate schedules. -/
def StochasticAlignmentCondition (w_star w : W ι) (η : ℕ → ℝ) (t : ℕ) (z μ : ℝ)
    (g_adv : Ω → W ι) : Prop :=
  let g_f (ω : Ω) := filteredGradient (g_adv ω) z
  Integrable g_f ∧
  Integrable (fun ω => ‖g_f ω‖ ^ 2) ∧
  2 * (η t) * (@inner ℝ _ _ (𝔼[g_f]) (w - w_star)) -
  (η t)^2 * 𝔼[fun ω => ‖g_f ω‖ ^ 2] ≥ (η t) * μ * ‖w - w_star‖ ^ 2

/-- **Integral Inner Product Identity**: The integral of an inner product with a
constant vector is the inner product of the integral. -/
lemma integral_inner_const {Ω : Type*} [MeasureSpace Ω]
    {f : Ω → W ι} (hf : Integrable f) (c : W ι) :
    (∫ ω, inner ℝ (f ω) c ∂volume) = inner ℝ (∫ ω, f ω ∂volume) c := by
  have : (fun ω => inner ℝ (f ω) c) = (fun ω => inner ℝ c (f ω)) :=
    by funext ω; rw [real_inner_comm]
  rw [this, integral_inner hf c, real_inner_comm]

/-- **Stochastic Distance Expansion**: The identity for the expected squared distance
after an update step: $𝔼[‖A - η_t • B‖ ^ 2] = ‖A‖ ^ 2 - 2η_t⟨𝔼[B], A⟩ +$
$η_t ^ 2 𝔼[‖B‖ ^ 2]$.
-/
lemma stochastic_dist_expansion (A : W ι) (B : Ω → W ι) (η : ℝ)
    (h_int_B : Integrable B) (h_int_B2 : Integrable (fun ω => ‖B ω‖ ^ 2)) :
    𝔼[fun ω => ‖A - η • B ω‖ ^ 2] =
      ‖A‖ ^ 2 - 2 * η * inner ℝ (𝔼[B]) A + η^2 * 𝔼[fun ω => ‖B ω‖ ^ 2] := by
  have h_int_1 : Integrable (fun ω => ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A) :=
    (integrable_const _).sub (h_int_B.inner_const A |>.const_mul (2 * η))
  have h_int_2 : Integrable (fun ω => η^2 * ‖B ω‖ ^ 2) := h_int_B2.const_mul (η^2)
  calc 𝔼[fun ω => ‖A - η • B ω‖ ^ 2]
    _ = 𝔼[fun ω => ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A + η^2 * ‖B ω‖ ^ 2] := by
        simp_rw [norm_sub_smul_sq]
    _ = 𝔼[fun ω => ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A] +
        𝔼[fun ω => η^2 * ‖B ω‖ ^ 2] :=
        integral_add h_int_1 h_int_2
    _ = ‖A‖ ^ 2 - 2 * η * 𝔼[fun ω => inner ℝ (B ω) A] +
        η ^ 2 * 𝔼[fun ω => ‖B ω‖ ^ 2] := by
        rw [integral_sub (integrable_const _) (h_int_B.inner_const A |>.const_mul (2 * η)),
            integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul]
    _ = ‖A‖ ^ 2 - 2 * η * inner ℝ (𝔼[B]) A + η ^ 2 * 𝔼[fun ω => ‖B ω‖ ^ 2] := by
        rw [integral_inner_const h_int_B A]

end LeanSharp
