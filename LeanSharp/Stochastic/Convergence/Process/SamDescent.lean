/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Process.Descent

/-!
# Stochastic SAM Descent

This module contains SAM-specific stochastic descent bounds built on the
general Z-score descent process.

## Main Theorems
* `sam_filtered_second_moment_le`: Perturbation-aware second-moment bound.
* `sam_stochastic_descent_step`: Complete perturbation-aware one-step bound.
* `sam_stochastic_descent_step_effective`: One-step bound in quarter-gradient
  effective-variance form.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory NNReal

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- The filtered update second moment is bounded by the noise variance and the
base-point gradient norm plus the smoothness error from the SAM perturbation. -/
theorem sam_filtered_second_moment_le
    (L : SmoothObjective ι) (g : Ω → W ι) (w : W ι)
    (ρ z σsq : ℝ) (hρ : 0 ≤ ρ)
    (h_stoch : IsStochasticGradient L.toFun g
      (w + samPerturbation L.toFun w ρ))
    (h_var : HasBoundedVariance L.toFun g
      (w + samPerturbation L.toFun w ρ) σsq)
    (h_int : Integrable (fun ω => ‖g ω‖ ^ 2) ℙ)
    (h_int_f : Integrable (fun ω => ‖filteredGradient (g ω) z‖ ^ 2) ℙ) :
    𝔼[fun ω => ‖filteredGradient (g ω) z‖ ^ 2] ≤
      σsq + (‖gradient L.toFun w‖ + (L.smoothness : ℝ) * ρ) ^ 2 := by
  have h_norm_le : 𝔼[fun ω => ‖filteredGradient (g ω) z‖ ^ 2] ≤
      𝔼[fun ω => ‖g ω‖ ^ 2] :=
    integral_mono h_int_f h_int (fun ω => norm_sq_filtered_gradient_le (g ω) z)
  have h_raw_decomp := l2_bias_variance_decomposition g h_int h_stoch.1
  rw [h_stoch.2] at h_raw_decomp
  have h_input_bound : 𝔼[fun ω => ‖g ω‖ ^ 2] ≤
      σsq + ‖gradient L.toFun (w + samPerturbation L.toFun w ρ)‖ ^ 2 := by
    rw [h_raw_decomp]
    unfold HasBoundedVariance at h_var
    linarith [h_var]
  have h_grad_diff := gradient_samPerturbation_error_le L w ρ hρ
  have h_grad_adv_norm :
      ‖gradient L.toFun (w + samPerturbation L.toFun w ρ)‖ ≤
        ‖gradient L.toFun w‖ + (L.smoothness : ℝ) * ρ := by
    calc
      ‖gradient L.toFun (w + samPerturbation L.toFun w ρ)‖ =
          ‖(gradient L.toFun (w + samPerturbation L.toFun w ρ) -
            gradient L.toFun w) + gradient L.toFun w‖ := by rw [sub_add_cancel]
      _ ≤ ‖gradient L.toFun (w + samPerturbation L.toFun w ρ) -
          gradient L.toFun w‖ + ‖gradient L.toFun w‖ := norm_add_le _ _
      _ ≤ ‖gradient L.toFun w‖ + (L.smoothness : ℝ) * ρ := by
        linarith
  have h_grad_adv_sq :
      ‖gradient L.toFun (w + samPerturbation L.toFun w ρ)‖ ^ 2 ≤
        (‖gradient L.toFun w‖ + (L.smoothness : ℝ) * ρ) ^ 2 := by
    have h_rhs_nonneg : 0 ≤ ‖gradient L.toFun w‖ + (L.smoothness : ℝ) * ρ :=
      add_nonneg (norm_nonneg _) (mul_nonneg L.smoothness.coe_nonneg hρ)
    have h_adv_nonneg : 0 ≤ ‖gradient L.toFun
        (w + samPerturbation L.toFun w ρ)‖ := norm_nonneg _
    nlinarith
  have h_second_adv : σsq + ‖gradient L.toFun
      (w + samPerturbation L.toFun w ρ)‖ ^ 2 ≤
      σsq + (‖gradient L.toFun w‖ + (L.smoothness : ℝ) * ρ) ^ 2 := by
    simpa only [add_comm] using add_le_add_left h_grad_adv_sq σsq
  exact h_norm_le.trans (h_input_bound.trans h_second_adv)

/-- **Complete SAM-filtered stochastic one-step bound**: Unbiasedness and
bounded variance at the perturbed point combine with base-point alignment to
give expected descent with an explicit `Lρ` perturbation error. -/
theorem sam_stochastic_descent_step
    (L : SmoothObjective ι) (g : Ω → W ι) (w : W ι)
    (η z ρ σsq : ℝ) (hρ : 0 ≤ ρ) (hη : 0 < η)
    (h_stoch : IsStochasticGradient L.toFun g
      (w + samPerturbation L.toFun w ρ))
    (h_var : HasBoundedVariance L.toFun g
      (w + samPerturbation L.toFun w ρ) σsq)
    (h_int : Integrable (fun ω => ‖g ω‖ ^ 2) ℙ)
    (h_meas_f : AEStronglyMeasurable (fun ω => filteredGradient (g ω) z) ℙ)
    (h_int_f : Integrable (fun ω => ‖filteredGradient (g ω) z‖ ^ 2) ℙ)
    (h_int_f_val : Integrable
      (fun ω => L.toFun (w - η • filteredGradient (g ω) z)) ℙ)
    (h_align : ‖gradient L.toFun w‖ ^ 2 ≤
      2 * inner ℝ (gradient L.toFun w)
        (𝔼[fun ω => filteredGradient (g ω) z])) :
    𝔼[fun ω => L.toFun (w - η • filteredGradient (g ω) z)] ≤
      L.toFun w - (η / 2) * ‖gradient L.toFun w‖ ^ 2 +
        (η ^ 2 * (L.smoothness : ℝ) / 2) *
          (σsq + (‖gradient L.toFun w‖ + (L.smoothness : ℝ) * ρ) ^ 2) := by
  have h_int_gf : Integrable (fun ω => filteredGradient (g ω) z) ℙ :=
    h_stoch.1.mono h_meas_f
      (Filter.Eventually.of_forall (fun ω => norm_filtered_gradient_le (g ω) z))
  have h_second := sam_filtered_second_moment_le L g w ρ z σsq hρ
    h_stoch h_var h_int h_int_f
  exact sam_expected_descent_step L g w η z ρ σsq hη h_int_gf h_int_f
    h_int_f_val h_second h_align

/-- **Effective-variance SAM one-step bound**: under the step-size condition
`η · L ≤ 1/4`, the perturbation-dependent second-moment term collapses to the
quarter-gradient form with effective variance `σ² + 2L²ρ²`, matching the
`SAMDescentEnvelope` interface. -/
theorem sam_stochastic_descent_step_effective
    (L : SmoothObjective ι) (g : Ω → W ι) (w : W ι)
    (η z ρ σsq : ℝ) (hρ : 0 ≤ ρ) (hη : 0 < η)
    (h_ηL : η * (L.smoothness : ℝ) ≤ 1 / 4)
    (h_stoch : IsStochasticGradient L.toFun g
      (w + samPerturbation L.toFun w ρ))
    (h_var : HasBoundedVariance L.toFun g
      (w + samPerturbation L.toFun w ρ) σsq)
    (h_int : Integrable (fun ω => ‖g ω‖ ^ 2) ℙ)
    (h_meas_f : AEStronglyMeasurable (fun ω => filteredGradient (g ω) z) ℙ)
    (h_int_f : Integrable (fun ω => ‖filteredGradient (g ω) z‖ ^ 2) ℙ)
    (h_int_f_val : Integrable
      (fun ω => L.toFun (w - η • filteredGradient (g ω) z)) ℙ)
    (h_align : ‖gradient L.toFun w‖ ^ 2 ≤
      2 * inner ℝ (gradient L.toFun w)
        (𝔼[fun ω => filteredGradient (g ω) z])) :
    𝔼[fun ω => L.toFun (w - η • filteredGradient (g ω) z)] ≤
      L.toFun w - (η / 4) * ‖gradient L.toFun w‖ ^ 2 +
        (η ^ 2 * (L.smoothness : ℝ) / 2) *
          (σsq + 2 * (L.smoothness : ℝ) ^ 2 * ρ ^ 2) := by
  have h_base := sam_stochastic_descent_step L g w η z ρ σsq hρ hη
    h_stoch h_var h_int h_meas_f h_int_f h_int_f_val h_align
  let Ls : ℝ := (L.smoothness : ℝ)
  have h_Ls_nonneg : 0 ≤ Ls := L.smoothness.coe_nonneg
  have h_sq_bound : (‖gradient L.toFun w‖ + Ls * ρ) ^ 2 ≤
      2 * ‖gradient L.toFun w‖ ^ 2 + 2 * (Ls * ρ) ^ 2 := by
    nlinarith [sq_nonneg (‖gradient L.toFun w‖ - Ls * ρ)]
  have h_mid_nonneg : 0 ≤ η ^ 2 * Ls / 2 := by
    positivity
  have h_eta_sq_L : η ^ 2 * Ls ≤ η / 4 := by
    have h_mul : η * (η * Ls) ≤ η * (1 / 4) :=
      mul_le_mul_of_nonneg_left h_ηL (le_of_lt hη)
    nlinarith
  have h_coeff : η ^ 2 * Ls - η / 2 ≤ - (η / 4) := by
    nlinarith [h_eta_sq_L]
  have h_grad_nonneg : 0 ≤ ‖gradient L.toFun w‖ ^ 2 := sq_nonneg _
  have h_grade : (η ^ 2 * Ls - η / 2) * ‖gradient L.toFun w‖ ^ 2 ≤
      - (η / 4) * ‖gradient L.toFun w‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h_coeff h_grad_nonneg
  calc
    𝔼[fun ω => L.toFun (w - η • filteredGradient (g ω) z)]
      ≤ L.toFun w - (η / 2) * ‖gradient L.toFun w‖ ^ 2 +
          (η ^ 2 * Ls / 2) * (σsq + (‖gradient L.toFun w‖ + Ls * ρ) ^ 2) := h_base
    _ ≤ L.toFun w - (η / 2) * ‖gradient L.toFun w‖ ^ 2 +
          (η ^ 2 * Ls / 2) * (σsq + 2 * ‖gradient L.toFun w‖ ^ 2 + 2 * (Ls * ρ) ^ 2) := by
      have hS : σsq + (‖gradient L.toFun w‖ + Ls * ρ) ^ 2 ≤
          σsq + 2 * ‖gradient L.toFun w‖ ^ 2 + 2 * (Ls * ρ) ^ 2 := by
        nlinarith [h_sq_bound]
      have hMul : (η ^ 2 * Ls / 2) * (σsq + (‖gradient L.toFun w‖ + Ls * ρ) ^ 2) ≤
          (η ^ 2 * Ls / 2) * (σsq + 2 * ‖gradient L.toFun w‖ ^ 2 + 2 * (Ls * ρ) ^ 2) :=
        mul_le_mul_of_nonneg_left hS h_mid_nonneg
      linarith
    _ = L.toFun w + (η ^ 2 * Ls - η / 2) * ‖gradient L.toFun w‖ ^ 2 +
          (η ^ 2 * Ls / 2) * (σsq + 2 * (Ls * ρ) ^ 2) := by ring
    _ ≤ L.toFun w - (η / 4) * ‖gradient L.toFun w‖ ^ 2 +
          (η ^ 2 * Ls / 2) * (σsq + 2 * (Ls * ρ) ^ 2) := by
      linarith [h_grade]
    _ = L.toFun w - (η / 4) * ‖gradient L.toFun w‖ ^ 2 +
          (η ^ 2 * Ls / 2) * (σsq + 2 * Ls ^ 2 * ρ ^ 2) := by ring

end LeanSharp
