/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Objective
import LeanSharp.Stochastic.Mechanics.SharpnessMap
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Notation

/-!
# Stochastic Descent Core

This module exists to isolate the foundational stochastic descent lemmas and
smoothness predicate needed by multiple stochastic descent interfaces.

## Definitions

* `IsSmooth`: smoothness predicate used by stochastic descent statements.

## Theorems

* `filtered_variance_bound`: filtering preserves bounded-variance control.
* `stochastic_taylor_descent`: expected one-step descent under smoothness.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Filtered Variance Bound**:
If a stochastic gradient $g$ has variance bounded by $\sigma^2$, then its
Z-score filtered version also has variance bounded by $\sigma^2$
(plus the squared norm of the true gradient).
This holds because the filter is a component-wise contraction toward zero. -/
theorem filtered_variance_bound (L : W ι → ℝ) (g : Ω → W ι) (w : W ι)
    (σsq : ℝ) (z : ℝ)
    (h_stoch : IsStochasticGradient L g w)
    (h_var : HasBoundedVariance L g w σsq)
    (h_int : Integrable (fun ω => ‖g ω‖ ^ 2))
    (h_meas_f : AEStronglyMeasurable (fun ω => filteredGradient (g ω) z))
    (h_int_f : Integrable (fun ω => ‖filteredGradient (g ω) z‖ ^ 2)) :
    𝔼[fun ω => ‖filteredGradient (g ω) z -
      𝔼[fun ω' => filteredGradient (g ω') z]‖ ^ 2] ≤
      σsq + ‖gradient L w‖ ^ 2 := by
  let g_f (ω : Ω) := filteredGradient (g ω) z
  have h_int_g : Integrable g := h_stoch.1
  have h_int_gf : Integrable g_f :=
    h_int_g.mono h_meas_f
      (Filter.Eventually.of_forall (fun ω => norm_filteredGradient_le (g ω) z))
  have h_gf_decomp := l2_bias_variance_decomposition g_f h_int_f h_int_gf
  have h_norm_le : 𝔼[fun ω => ‖g_f ω‖ ^ 2] ≤ 𝔼[fun ω => ‖g ω‖ ^ 2] :=
    integral_mono h_int_f h_int (fun ω => norm_sq_filteredGradient_le (g ω) z)
  have h_raw_decomp := l2_bias_variance_decomposition g h_int h_stoch.1
  calc 𝔼[fun ω => ‖g_f ω - 𝔼[g_f]‖ ^ 2]
    _ = 𝔼[fun ω => ‖g_f ω‖ ^ 2] - ‖𝔼[g_f]‖ ^ 2 := by
        rw [h_gf_decomp]
        ring
    _ ≤ 𝔼[fun ω => ‖g_f ω‖ ^ 2] := by
        simp only [sub_le_self_iff]
        positivity
    _ ≤ 𝔼[fun ω => ‖g ω‖ ^ 2] := h_norm_le
    _ = 𝔼[fun ω => ‖g ω - 𝔼[g]‖ ^ 2] + ‖𝔼[g]‖ ^ 2 := h_raw_decomp
    _ ≤ σsq + ‖gradient L w‖ ^ 2 := by
        rw [h_stoch.2, add_comm _ (‖gradient L w‖ ^ 2), add_comm σsq]
        apply add_le_add_right h_var

/-- A function is $L$-smooth if its gradient is $L$-Lipschitz.
This implies the Taylor-like bound used in the descent lemma. -/
def IsSmooth (f : W ι → ℝ) (L : ℝ) : Prop :=
  ∀ x y, f y ≤ f x + inner ℝ (gradient f x) (y - x) + (L / 2) * ‖y - x‖ ^ 2

/-- **Stochastic Taylor Descent**:
The fundamental descent lemma for a smooth function under stochastic gradients.
For an $L$-smooth function $f$, a single step of SGD with step size $\eta \le 1/L$
satisfies an expected decrease proportional to the gradient norm, scaled by the
variance of the estimator. -/
theorem stochastic_taylor_descent (L_smooth : ℝ) (f : W ι → ℝ) (g : Ω → W ι)
    (w : W ι) (η : ℝ)
    (h_smooth : IsSmooth f L_smooth)
    (h_stoch : IsStochasticGradient f g w)
    (h_int : Integrable (fun ω => ‖g ω‖ ^ 2) ℙ)
    (h_η : 0 < η ∧ η ≤ 1 / L_smooth)
    (h_int_f : Integrable (fun ω => f (w - η • g ω)) ℙ) :
    𝔼[fun ω => f (w - η • g ω)] ≤
      f w - (η / 2) * ‖gradient f w‖ ^ 2 +
      (η ^ 2 * L_smooth / 2) * 𝔼[fun ω => ‖g ω - gradient f w‖ ^ 2] := by
  have h_taylor_loc (ω : Ω) :
      f (w - η • g ω) ≤ f w + inner ℝ (gradient f w) (w - η • g ω - w) +
      (L_smooth / 2) * ‖w - η • g ω - w‖ ^ 2 :=
    h_smooth w (w - η • g ω)
  have h_simp (ω : Ω) : f (w - η • g ω) ≤ f w - η * inner ℝ (gradient f w) (g ω) +
      (η ^ 2 * L_smooth / 2) * ‖g ω‖ ^ 2 := by
    have h_diff : w - η • g ω - w = -η • g ω := by simp only [sub_sub_cancel_left, neg_smul]
    have h_point := h_taylor_loc ω
    rw [h_diff] at h_point
    have h_term1 : inner ℝ (gradient f w) (-η • g ω) =
        -η * inner ℝ (gradient f w) (g ω) := by
      rw [inner_smul_right, real_inner_comm]
    have h_term2 : ‖-η • g ω‖ ^ 2 = η ^ 2 * ‖g ω‖ ^ 2 := by
      simp only [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    calc f (w - η • g ω)
      _ ≤ f w + inner ℝ (gradient f w) (-η • g ω) +
          (L_smooth / 2) * ‖-η • g ω‖ ^ 2 := h_point
      _ = f w - η * inner ℝ (gradient f w) (g ω) +
          (η ^ 2 * L_smooth / 2) * ‖g ω‖ ^ 2 := by
          rw [h_term1, h_term2]
          ring
  have h_int_rhs : Integrable (fun ω => f w - η * inner ℝ (gradient f w) (g ω) +
      (η^2 * L_smooth / 2) * ‖g ω‖ ^ 2) ℙ := by
    apply Integrable.add
    · apply Integrable.sub
      · apply integrable_const
      · apply Integrable.const_mul
        let h_int_inner := Integrable.inner_const (𝕜 := ℝ) h_stoch.1 (gradient f w)
        apply h_int_inner.congr
        exact (Filter.Eventually.of_forall fun ω => real_inner_comm _ _)
    · exact Integrable.const_mul h_int (η ^ 2 * L_smooth / 2)
  have h_int_le : 𝔼[fun ω => f (w - η • g ω)] ≤
      𝔼[fun ω => f w - η * inner ℝ (gradient f w) (g ω) +
        (η^2 * L_smooth / 2) * ‖g ω‖ ^ 2] :=
    integral_mono h_int_f h_int_rhs h_simp
  have h_exp_rhs : 𝔼[fun ω => f w - η * inner ℝ (gradient f w) (g ω)
      + (η ^ 2 * L_smooth / 2) * ‖g ω‖ ^ 2]
      = f w - η * ‖gradient f w‖ ^ 2 + (η ^ 2 * L_smooth / 2)
      * 𝔼[fun ω => ‖g ω‖ ^ 2] := by
    have h1 : ∫ (ω : Ω), f w ∂ℙ = f w := by
      simp only [integral_const, probReal_univ, one_smul]
    have h2 : ∫ (ω : Ω), η * inner ℝ (gradient f w) (g ω) ∂ℙ =
        η * ‖gradient f w‖ ^ 2 := by
      calc ∫ ω, η * inner ℝ (gradient f w) (g ω) ∂ℙ
        _ = η * ∫ ω, inner ℝ (gradient f w) (g ω) ∂ℙ := integral_const_mul η _
        _ = η * inner ℝ (gradient f w) (∫ ω, g ω ∂ℙ) := by
          congr 1; exact integral_inner h_stoch.1 (gradient f w)
        _ = η * inner ℝ (gradient f w) (gradient f w) := by rw [h_stoch.2]
        _ = η * ‖gradient f w‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have h3 : ∫ (ω : Ω), (η ^ 2 * L_smooth / 2) * ‖g ω‖ ^ 2 ∂ℙ =
        (η ^ 2 * L_smooth / 2) * ∫ (ω : Ω), ‖g ω‖ ^ 2 ∂ℙ :=
      integral_const_mul _ (fun (ω : Ω) => ‖g ω‖ ^ 2)
    have h_int1 : Integrable (fun (_ : Ω) => f w) ℙ := integrable_const _
    have h_int2_inner := (Integrable.inner_const h_stoch.1 (gradient f w)).const_mul η
    have h_int2 : Integrable (fun ω => η * inner ℝ (gradient f w) (g ω)) ℙ :=
      h_int2_inner.congr (Filter.Eventually.of_forall (fun ω => by
        dsimp only; rw [real_inner_comm]))
    calc ∫ ω, f w - η * inner ℝ (gradient f w) (g ω) +
          (η ^ 2 * L_smooth / 2) * ‖g ω‖ ^ 2 ∂ℙ
      _ = ∫ ω, (f w - η * inner ℝ (gradient f w) (g ω)) +
          (η ^ 2 * L_smooth / 2) * ‖g ω‖ ^ 2 ∂ℙ := rfl
      _ = ∫ ω, (f w - η * inner ℝ (gradient f w) (g ω)) ∂ℙ +
          ∫ ω, (η ^ 2 * L_smooth / 2) * ‖g ω‖ ^ 2 ∂ℙ :=
          integral_add (h_int1.sub h_int2) (Integrable.const_mul h_int _)
      _ = ∫ ω, f w ∂ℙ - ∫ ω, η * inner ℝ (gradient f w) (g ω) ∂ℙ +
          ∫ ω, (η ^ 2 * L_smooth / 2) * ‖g ω‖ ^ 2 ∂ℙ :=
          by rw [integral_sub h_int1 h_int2]
      _ = f w - η * ‖gradient f w‖ ^ 2 +
          (η ^ 2 * L_smooth / 2) * 𝔼[fun ω => ‖g ω‖ ^ 2] :=
          by rw [h1, h2, h3]
  rw [h_exp_rhs] at h_int_le
  have h_decomp := l2_bias_variance_decomposition g h_int h_stoch.1
  rw [h_stoch.2] at h_decomp
  let term_var := 𝔼[fun ω => ‖g ω - gradient f w‖ ^ 2]
  let term_grad := ‖gradient f w‖ ^ 2
  calc 𝔼[fun ω => f (w - η • g ω)]
    _ ≤ f w - η * term_grad + (η ^ 2 * L_smooth / 2) * (term_var + term_grad) := by
        convert h_int_le using 1; rw [h_decomp]
    _ = f w - (η - η ^ 2 * L_smooth / 2) * term_grad +
        (η ^ 2 * L_smooth / 2) * term_var := by ring
    _ ≤ f w - (η / 2) * term_grad + (η ^ 2 * L_smooth / 2) * term_var := by
        have h_L_pos : 0 < L_smooth := by
          have h_inv_pos : 0 < 1 / L_smooth := h_η.1.trans_le h_η.2
          exact one_div_pos.mp h_inv_pos
        have h_eta_L : η * L_smooth ≤ 1 := (le_div_iff₀ h_L_pos).mp h_η.2
        have h_bound : η / 2 ≤ η - η ^ 2 * L_smooth / 2 := by
          calc η / 2 = η * (1 / 2) := by ring
            _ ≤ η * (1 - η * L_smooth / 2) := by
                apply mul_le_mul_of_nonneg_left _ h_η.1.le; linarith [h_eta_L]
            _ = η - η ^ 2 * L_smooth / 2 := by ring
        have h_grad_nonneg : 0 ≤ term_grad := sq_nonneg _
        nlinarith [h_bound, h_grad_nonneg]

end LeanSharp
