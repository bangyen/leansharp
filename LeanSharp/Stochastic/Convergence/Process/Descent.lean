/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Process.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stochastic ZSharp Process - Descent Analysis

This module establishes one-step expected descent inequalities and the core
stochastic convergence theorem for ZSharp.

## Main Theorems
* `one_step_descent`: Single-step progress bound.
* `stochastic_convergence`: Martingale-based convergence theorem.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory NNReal

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **One-step expected descent inequality**: converts an almost-everywhere conditional
descent statement for step `t` into an unconditional expectation inequality. This theorem
exists to provide a reusable bridge for sequence-level convergence arguments. -/
theorem stochastic_expected_descent_step
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ) (t : ℕ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (h_step_t : ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochasticZSharpStep (w t ω) η t z (g_adv t) ω)
    (h_desc_step_t : ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochasticZSharpStep (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int_t : Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad_t : Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas_t : ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    ∫ ω, f (w (t + 1) ω) ∂ℙ ≤
      ∫ ω, f (w t ω) ∂ℙ - (η t / 4) * ∫ ω, ‖gradient f (w t ω)‖ ^ 2 ∂ℙ +
      (η t ^ 2 * L_smooth / 2) * σsq := by
  rw [← integral_condExp h_meas_t]
  have h_step_ae : ∀ᵐ ω ∂ℙ, f (w (t + 1) ω)
      = f (stochasticZSharpStep (w t ω) η t z (g_adv t) ω) := by
    filter_upwards [h_step_t] with ω h
    rw [h]
  have h_cond_exp_eq : volume[fun ω' => f (w (t + 1) ω') | ℱ t] =ᵐ[ℙ]
      volume[fun ω' => f (stochasticZSharpStep (w t ω') η t z (g_adv t) ω') | ℱ t] := by
    apply condExp_congr_ae h_step_ae
  have h_bound_ae : volume[fun ω' => f (w (t + 1) ω') | ℱ t] ≤ᵐ[ℙ]
      (fun ω => f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2
      + (η t ^ 2 * L_smooth / 2) * σsq) := by
    apply h_cond_exp_eq.trans_le h_desc_step_t
  have h_int1 : Integrable
    (fun ω => f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2) ℙ :=
    h_int_t.sub
      (h_int_grad_t.const_mul _)
  have h_int2 : Integrable (fun (_ : Ω) => (η t ^ 2 * L_smooth / 2) * σsq) ℙ :=
    integrable_const _
  have h_int_rhs : Integrable (fun ω => f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2
    + (η t ^ 2 * L_smooth / 2) * σsq) ℙ := h_int1.add h_int2
  have h_integral_le := integral_mono_ae integrable_condExp h_int_rhs h_bound_ae
  rw [integral_add h_int1 h_int2] at h_integral_le
  rw [integral_sub h_int_t (h_int_grad_t.const_mul _)] at h_integral_le
  rw [integral_const (η t ^ 2 * L_smooth / 2 * σsq), probReal_univ, one_smul,
      integral_const_mul] at h_integral_le
  exact h_integral_le

/-- **Stochastic ZSharp Convergence Theorem**: Under the stochastic alignment
condition and standard assumptions, the distance to the optimum decreases in
expectation under a learning rate schedule. -/
theorem stochastic_zsharp_convergence (w_star : W ι) {g_adv : Ω → W ι} (w : W ι)
    (η : ℕ → ℝ) (t : ℕ) (z μ : ℝ)
    (h_align : StochasticAlignmentCondition w_star w η t z μ g_adv) :
    𝔼[fun ω => ‖stochasticZSharpStep w η t z g_adv ω - w_star‖ ^ 2] ≤
      (1 - (η t) * μ) * ‖w - w_star‖ ^ 2 := by
  let A : W ι := w - w_star
  let B (ω : Ω) : W ι := filteredGradient (g_adv ω) z
  have hrw : ∀ ω, stochasticZSharpStep w η t z g_adv ω - w_star = A - (η t) • B ω := by
    intro ω; unfold stochasticZSharpStep A B
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

theorem z_score_descent_fixed (L_smooth : ℝ) (f : W ι → ℝ) (g : Ω → W ι) (w : W ι)
    (η z : ℝ) (σsq : ℝ)
    (h_smooth : IsSmooth f L_smooth)
    (h_stoch : IsStochasticGradient f g w)
    (h_var : HasBoundedVariance f g w σsq)
    (h_int : Integrable (fun ω => ‖g ω‖ ^ 2) ℙ)
    (h_η : 0 < η ∧ η ≤ 1 / (2 * L_smooth))
    (h_meas_f : AEStronglyMeasurable (fun ω => filteredGradient (g ω) z) ℙ)
    (h_int_f : Integrable (fun ω => ‖filteredGradient (g ω) z‖ ^ 2) ℙ)
    (h_int_f_val : Integrable (fun ω => f (w - η • filteredGradient (g ω) z)) ℙ)
    (h_align : ‖gradient f w‖ ^ 2 ≤
      2 * inner ℝ (gradient f w) (𝔼[fun ω => filteredGradient (g ω) z])) :
    𝔼[fun ω => f (w - η • filteredGradient (g ω) z)] ≤
      f w - (η / 4) * ‖gradient f w‖ ^ 2 + (η ^ 2 * L_smooth / 2) * σsq := by
  have h_η_pos := h_η.1
  have h_η_le := h_η.2
  have h_L_pos : 0 < L_smooth := by
    by_contra h_le_zero; push_neg at h_le_zero
    if h_zero : L_smooth = 0 then
      rw [h_zero] at h_η_le; norm_num at h_η_le; linarith
    else
      have h_neg : L_smooth < 0 := lt_of_le_of_ne h_le_zero h_zero
      have : 1 / (2 * L_smooth) < 0 := by apply div_neg_of_pos_of_neg <;> linarith
      linarith
  have h_η_orig : η ≤ 1 / L_smooth :=
    h_η_le.trans (by apply one_div_le_one_div_of_le h_L_pos; linarith)
  have h_descent := z_score_descent L_smooth f g w η z σsq
    h_smooth h_stoch h_var h_int ⟨h_η_pos, h_η_orig⟩ h_meas_f h_int_f h_int_f_val h_align
  calc 𝔼[fun ω => f (w - η • filteredGradient (g ω) z)]
    _ ≤ f w - (η / 2) * ‖gradient f w‖ ^ 2 +
        (η ^ 2 * L_smooth / 2) * (σsq + ‖gradient f w‖ ^ 2) := h_descent
    _ = f w - (η / 2 - η ^ 2 * L_smooth / 2) * ‖gradient f w‖ ^ 2 +
        (η ^ 2 * L_smooth / 2) * σsq := by ring
    _ ≤ f w - (η / 4) * ‖gradient f w‖ ^ 2 + (η ^ 2 * L_smooth / 2) * σsq := by
      simp only [add_le_add_iff_right, sub_le_sub_iff_left]
      have h_ηL : η * L_smooth ≤ 1 / 2 := by
        have h_pos : 2 * L_smooth > 0 := by linarith [h_L_pos]
        have h_le := h_η_le
        rw [le_div_iff₀ h_pos] at h_le
        nlinarith
      have h_factor : η / 4 ≤ η / 2 - η ^ 2 * L_smooth / 2 := by
        nlinarith [h_η_pos, h_ηL]
      apply mul_le_mul_of_nonneg_right h_factor (pow_two_nonneg _)

end LeanSharp
