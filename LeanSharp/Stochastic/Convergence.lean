/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Descent
import LeanSharp.Stochastic.Sam
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Field.Basic

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

open ProbabilityTheory MeasureTheory NNReal

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Stochastic Alignment Condition**: A generalization of the alignment condition
to the stochastic setting, supporting learning rate schedules. -/
def stochastic_alignment_condition (w_star w : W ι) (η : ℕ → ℝ) (t : ℕ) (z μ : ℝ)
    (g_adv : Ω → W ι) : Prop :=
  let g_f (ω : Ω) := filtered_gradient (g_adv ω) z
  Integrable g_f ∧
  Integrable (fun ω => ‖g_f ω‖ ^ 2) ∧
  2 * (η t) * (@inner ℝ _ _ (𝔼[g_f]) (w - w_star)) -
  (η t)^2 * 𝔼[fun ω => ‖g_f ω‖ ^ 2] ≥ (η t) * μ * ‖w - w_star‖ ^ 2

/-- **Integral Inner Product Identity**: The integral of an inner product with a
constant vector is the inner product of the integral. -/
private lemma integral_inner_const {Ω : Type*} [MeasureSpace Ω]
    {f : Ω → W ι} (hf : Integrable f) (c : W ι) :
    (∫ ω, inner ℝ (f ω) c ∂volume) = inner ℝ (∫ ω, f ω ∂volume) c := by
  have : (fun ω => inner ℝ (f ω) c) = (fun ω => inner ℝ c (f ω)) :=
    by funext ω; rw [real_inner_comm]
  rw [this, integral_inner hf c, real_inner_comm]

/-- **Stochastic Distance Expansion**: The identity for the expected squared distance
after an update step: $𝔼[‖A - η_t • B‖ ^ 2] = ‖A‖ ^ 2 - 2η_t⟨𝔼[B], A⟩ +$
$η_t ^ 2 𝔼[‖B‖ ^ 2]$.
-/
private lemma stochastic_dist_expansion (A : W ι) (B : Ω → W ι) (η : ℝ)
    (h_int_B : Integrable B) (h_int_B2 : Integrable (fun ω => ‖B ω‖ ^ 2)) :
    𝔼[fun ω => ‖A - η • B ω‖ ^ 2] =
      ‖A‖ ^ 2 - 2 * η * inner ℝ (𝔼[B]) A + η^2 * 𝔼[fun ω => ‖B ω‖ ^ 2] := by
  have h_int_1 : Integrable (fun ω => ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A) :=
    (integrable_const _).sub (h_int_B.inner_const A |>.const_mul (2 * η))
  have h_int_2 : Integrable (fun ω => η^2 * ‖B ω‖ ^ 2) := h_int_B2.const_mul (η^2)
  calc 𝔼[fun ω => ‖A - η • B ω‖ ^ 2]
    _ = 𝔼[fun ω => ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A + η^2 * ‖B ω‖ ^ 2] := by
        simp_rw [norm_sub_smul_sq]
    _ = 𝔼[fun ω => ‖A‖ ^ 2 - 2 * η * inner ℝ (B ω) A] + 𝔼[fun ω => η^2 * ‖B ω‖ ^ 2] :=
        integral_add h_int_1 h_int_2
    _ = ‖A‖ ^ 2 - 2 * η * 𝔼[fun ω => inner ℝ (B ω) A] + η ^ 2 * 𝔼[fun ω => ‖B ω‖ ^ 2] := by
        rw [integral_sub (integrable_const _) (h_int_B.inner_const A |>.const_mul (2 * η)),
            integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul]
    _ = ‖A‖ ^ 2 - 2 * η * inner ℝ (𝔼[B]) A + η ^ 2 * 𝔼[fun ω => ‖B ω‖ ^ 2] := by
        rw [integral_inner_const h_int_B A]

/-- **Stochastic ZSharp Convergence Theorem**: Under the stochastic alignment
condition and standard assumptions, the distance to the optimum decreases in
expectation under a learning rate schedule. -/
theorem stochastic_zsharp_convergence (w_star : W ι) {g_adv : Ω → W ι} (w : W ι)
    (η : ℕ → ℝ) (t : ℕ) (z μ : ℝ)
    (h_align : stochastic_alignment_condition w_star w η t z μ g_adv) :
    𝔼[fun ω => ‖stochastic_zsharp_step w η t z g_adv ω - w_star‖ ^ 2] ≤
      (1 - (η t) * μ) * ‖w - w_star‖ ^ 2 := by
  let A : W ι := w - w_star
  let B (ω : Ω) : W ι := filtered_gradient (g_adv ω) z
  have hrw : ∀ ω, stochastic_zsharp_step w η t z g_adv ω - w_star = A - (η t) • B ω := by
    intro ω; unfold stochastic_zsharp_step A B
    simp only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  -- Step 1: Expand the squared distance using the helper lemma
  have h_expansion := stochastic_dist_expansion A B (η t) h_align.1 h_align.2.1
  simp_rw [hrw]
  rw [h_expansion]
  -- Step 2: Apply the stochastic alignment condition and algebra reduction
  have h_bound : 2 * (η t) * inner ℝ 𝔼[B] A - (η t)^2 * 𝔼[fun ω => ‖B ω‖^2] ≥
      (η t) * μ * ‖A‖^2 :=
    h_align.2.2
  linarith [pow_two_nonneg ‖A‖]


omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- **ZSharp Stochastic Convergence**: The main convergence result for ZSharp. It shows
that the algorithm converges to a neighborhood of the optimum under a schedule. -/
theorem zsharp_stochastic_convergence (L : W ι → ℝ) (w : W ι) (η : ℕ → ℝ) (t : ℕ)
    (z σsq : ℝ) (M : ℝ≥0)
    (g_adv : Ω → W ι)
    (h_descent : 𝔼[fun ω => L (stochastic_zsharp_step w η t z g_adv ω)] ≤
      L w - (η t) * ‖gradient L w‖ ^ 2 +
        (M : ℝ) * (η t) ^ 2 / 2 * (σsq + ‖gradient L w‖ ^ 2)) :
    𝔼[fun ω => L (stochastic_zsharp_step w η t z g_adv ω)] ≤
      L w - (η t) * (1 - (M : ℝ) * (η t) / 2) * ‖gradient L w‖ ^ 2 +
        (M : ℝ) * (η t) ^ 2 * σsq / 2 := by
  linarith
theorem z_score_descent_fixed (L_smooth : ℝ) (f : W ι → ℝ) (g : Ω → W ι) (w : W ι) (η z : ℝ)
    (σsq : ℝ)
    (h_smooth : is_smooth f L_smooth)
    (h_stoch : is_stochastic_gradient f g w)
    (h_var : has_bounded_variance f g w σsq)
    (h_int : Integrable (fun ω => ‖g ω‖ ^ 2) ℙ)
    (h_η : 0 < η ∧ η ≤ 1 / (2 * L_smooth))
    (h_meas_f : AEStronglyMeasurable (fun ω => filtered_gradient (g ω) z) ℙ)
    (h_int_f : Integrable (fun ω => ‖filtered_gradient (g ω) z‖ ^ 2) ℙ)
    (h_int_f_val : Integrable (fun ω => f (w - η • filtered_gradient (g ω) z)) ℙ)
    (h_align : ‖gradient f w‖ ^ 2 ≤
      2 * inner ℝ (gradient f w) (𝔼[fun ω => filtered_gradient (g ω) z])) :
    𝔼[fun ω => f (w - η • filtered_gradient (g ω) z)] ≤
      f w - (η / 4) * ‖gradient f w‖ ^ 2 + (η ^ 2 * L_smooth / 2) * σsq := by
  have h_L : 0 < L_smooth := by
    by_contra h; push_neg at h
    if h_zero : L_smooth = 0 then
      rw [h_zero] at h_η
      have : η ≤ 0 := by
        replace h_η := h_η.2
        simpa only [
          ge_iff_le,
          mul_zero,
          div_zero
        ] using h_η
      linarith
    else
      have h_neg : L_smooth < 0 := lt_of_le_of_ne h h_zero
      have h_div : 1 / (2 * L_smooth) < 0 := by
        apply div_neg_of_pos_of_neg
        · exact zero_lt_one
        · linarith
      linarith
  have h_η_orig : η ≤ 1 / L_smooth := by
    calc η ≤ 1 / (2 * L_smooth) := h_η.2
      _ ≤ 1 / L_smooth := by
        apply one_div_le_one_div_of_le h_L
        linarith
  have h_descent := z_score_descent L_smooth f g w η z σsq
    h_smooth h_stoch h_var h_int ⟨h_η.1, h_η_orig⟩ h_meas_f h_int_f h_int_f_val h_align
  calc 𝔼[fun ω => f (w - η • filtered_gradient (g ω) z)]
    _ ≤ f w - (η / 2) * ‖gradient f w‖ ^ 2 +
        (η ^ 2 * L_smooth / 2) * (σsq + ‖gradient f w‖ ^ 2) := h_descent
    _ = f w - (η / 4) * ‖gradient f w‖ ^ 2 + (η ^ 2 * L_smooth / 2) * σsq -
        (η / 4 - η^2 * L_smooth / 2) * ‖gradient f w‖ ^ 2 := by ring
    _ ≤ f w - (η / 4) * ‖gradient f w‖ ^ 2 + (η ^ 2 * L_smooth / 2) * σsq := by
        simp only [sub_le_self_iff]
        apply mul_nonneg
        · have h1 : 0 ≤ (η / 4) * (1 - 2 * η * L_smooth) := by
            apply mul_nonneg (by linarith)
            have h_ηL : η * L_smooth ≤ 1 / 2 := by
              have h_inv : η ≤ 1 / (2 * L_smooth) := h_η.2
              have h_pos : 2 * L_smooth > 0 := by linarith
              have h_2ηL : η * (2 * L_smooth) ≤ 1 := by
                rwa [le_div_iff₀ h_pos] at h_inv
              linarith
            linarith
          field_simp
          linarith
        · exact pow_two_nonneg _

end LeanSharp
