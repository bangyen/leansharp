/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Mechanics.DescentSteps.Core

/-!
# Z-Score Descent Interface

This module exists to isolate the z-score filtered descent theorem so callers
can depend on the high-level filtered result without importing all core proofs.

## Theorems

* `z_score_descent`: descent inequality for z-score filtered stochastic gradients.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Z-Score Descent Lemma**:
The final descent lemma for Z-score filtered gradients. -/
theorem z_score_descent (L_smooth : ℝ) (f : W ι → ℝ) (g : Ω → W ι) (w : W ι)
    (η z : ℝ) (σsq : ℝ)
    (h_smooth : IsSmooth f L_smooth)
    (h_stoch : IsStochasticGradient f g w)
    (h_var : HasBoundedVariance f g w σsq)
    (h_int : Integrable (fun ω => ‖g ω‖ ^ 2) ℙ)
    (h_η : 0 < η ∧ η ≤ 1 / L_smooth)
    (h_meas_f : AEStronglyMeasurable (fun ω => filteredGradient (g ω) z) ℙ)
    (h_int_f : Integrable (fun ω => ‖filteredGradient (g ω) z‖ ^ 2) ℙ)
    (h_int_f_val : Integrable (fun ω => f (w - η • filteredGradient (g ω) z)) ℙ)
    (h_align : ‖gradient f w‖ ^ 2 ≤
      2 * inner ℝ (gradient f w) (𝔼[fun ω => filteredGradient (g ω) z])) :
    𝔼[fun ω => f (w - η • filteredGradient (g ω) z)] ≤
      f w - (η / 2) * ‖gradient f w‖ ^ 2 +
      (η ^ 2 * L_smooth / 2) * (σsq + ‖gradient f w‖ ^ 2) := by
  let g_f_loc (ω : Ω) := filteredGradient (g ω) z
  have h_norm_le : 𝔼[fun ω => ‖g_f_loc ω‖ ^ 2] ≤ 𝔼[fun ω => ‖g ω‖ ^ 2] :=
    integral_mono h_int_f h_int (fun ω => norm_sq_filteredGradient_le (g ω) z)
  have h_raw_decomp := l2_bias_variance_decomposition g h_int h_stoch.1
  rw [h_stoch.2] at h_raw_decomp
  have h_input_bound : 𝔼[fun ω => ‖g ω‖ ^ 2] ≤ σsq + ‖gradient f w‖ ^ 2 := by
    rw [h_raw_decomp]; unfold HasBoundedVariance at h_var; linarith [h_var]
  have h_int_gf : Integrable g_f_loc ℙ :=
    h_stoch.1.mono h_meas_f
      (Filter.Eventually.of_forall (fun ω => norm_filteredGradient_le (g ω) z))
  have h_int_inner : Integrable (fun ω => η * inner ℝ (gradient f w) (g_f_loc ω)) ℙ := by
    apply (Integrable.inner_const h_int_gf (gradient f w)).const_mul η |>.congr
    apply Filter.Eventually.of_forall; intro ω; dsimp only; rw [real_inner_comm]
  have h_int_rhs : Integrable (fun ω => f w - η * inner ℝ (gradient f w) (g_f_loc ω) +
      (η^2 * L_smooth / 2) * ‖g_f_loc ω‖ ^ 2) ℙ :=
    (integrable_const (f w) |>.sub h_int_inner).add (h_int_f.const_mul _)
  have h_simp_f (ω : Ω) :
      f (w - η • g_f_loc ω) ≤ f w - η * inner ℝ (gradient f w) (g_f_loc ω) +
      (η ^ 2 * L_smooth / 2) * ‖g_f_loc ω‖ ^ 2 := by
    have h_taylor := h_smooth w (w - η • g_f_loc ω)
    have h_diff : w - η • g_f_loc ω - w = -η • g_f_loc ω :=
      by simp only [sub_sub_cancel_left, neg_smul]
    rw [h_diff] at h_taylor
    have h_term1 : inner ℝ (gradient f w) (-η • g_f_loc ω) =
        -η * inner ℝ (gradient f w) (g_f_loc ω) := by
      rw [inner_smul_right, real_inner_comm]
    have h_term2 : ‖-η • g_f_loc ω‖ ^ 2 = η ^ 2 * ‖g_f_loc ω‖ ^ 2 := by
      simp only [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [h_term1, h_term2] at h_taylor
    linarith
  have h_int_le : 𝔼[fun ω => f (w - η • g_f_loc ω)] ≤
      𝔼[fun ω => f w - η * inner ℝ (gradient f w) (g_f_loc ω) +
      (η ^ 2 * L_smooth / 2) * ‖g_f_loc ω‖ ^ 2] :=
    integral_mono h_int_f_val h_int_rhs h_simp_f
  have h_exp_rhs : 𝔼[fun ω => f w - η * inner ℝ (gradient f w) (g_f_loc ω) +
      (η ^ 2 * L_smooth / 2) * ‖g_f_loc ω‖ ^ 2] =
      f w - η * inner ℝ (gradient f w) (𝔼[g_f_loc]) +
      (η ^ 2 * L_smooth / 2) * 𝔼[fun ω => ‖g_f_loc ω‖ ^ 2] := by
    have h_int_c : Integrable (fun (_ : Ω) => f w) ℙ := integrable_const _
    have h_part1 : Integrable (fun ω => f w -
        η * inner ℝ (gradient f w) (g_f_loc ω)) ℙ :=
      h_int_c.sub h_int_inner
    rw [integral_add h_part1 (h_int_f.const_mul _)]
    rw [integral_sub h_int_c h_int_inner, integral_const,
        probReal_univ, one_smul, integral_const_mul]
    rw [integral_const_mul, real_inner_comm]
    congr 2; rw [integral_inner h_int_gf (gradient f w), real_inner_comm]
  rw [h_exp_rhs] at h_int_le
  let G := ‖gradient f w‖ ^ 2
  let V_f := 𝔼[fun ω => ‖g_f_loc ω‖ ^ 2]
  let I_f := inner ℝ (gradient f w) (𝔼[g_f_loc])
  have h_ps : - η * I_f ≤ - (η / 2) * G := by
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    calc η * I_f = (η / 2) * (2 * I_f) := by ring
      _ ≥ (η / 2) * G := by
        apply mul_le_mul_of_nonneg_left h_align
        linarith [h_η.1]
  have h_vs : (η ^ 2 * L_smooth / 2) * V_f ≤ (η ^ 2 * L_smooth / 2) * (σsq + G) := by
    apply mul_le_mul_of_nonneg_left (h_norm_le.trans h_input_bound)
    have h_L_pos : 0 < L_smooth := by
      have h_inv_pos : 0 < 1 / L_smooth := h_η.1.trans_le h_η.2
      exact one_div_pos.mp h_inv_pos
    positivity
  linarith [h_int_le, h_ps, h_vs]

end LeanSharp
