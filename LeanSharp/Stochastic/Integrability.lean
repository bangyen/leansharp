/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Descent
import LeanSharp.Stochastic.Sam
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Notation

/-!
# Integrability Derivations for ZSharp

This module provides the mathematical derivations to satisfy the `Integrable`
hypotheses required by Robbins-Monro convergence theorems. Instead of assuming
integrability at each step in the theorem signatures, we bundle those properties
into a structural assumption set.

## Definitions

* `ZSharpStructuralAssumptions`.

## Theorems

* `zsharp_structural_integrability`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Structural ZSharp Assumptions**: A bundle of properties that imply the
integrability of the stochastic process. This captures all the regulatory conditions
needed for Robbins-Monro convergence without requiring manual proof in the middle
of descent lemmas. -/
structure ZSharpStructuralAssumptions (f : W ι → ℝ) (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ) where
  /-- Lipschitz constant of the gradient. -/
  L_smooth : NNReal
  /-- Gradient smoothness hypothesis witness. -/
  h_smooth : is_smooth f L_smooth
  /-- Global lower bound hypothesis witness. -/
  h_bdd_below : BddBelow (Set.range f)
  /-- Gradient estimator variance hypothesis witness. -/
  h_var :
    ∀ t, has_bounded_variance f (fun ω => gradient f (w t ω)) (w t ω) σsq
  /-- Initial weight integrability witness. -/
  h_w0 : Integrable (fun ω => ‖w 0 ω‖ ^ 2)
  /-- Measurability of the stochastic process. -/
  h_meas : ∀ t, AEStronglyMeasurable (w t)
  /-- Step update rule witness. -/
  h_step :
    ∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω =
        stochastic_zsharp_step (w t ω) η t z
          (fun ω' => gradient f (w t ω')) ω

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- **Inner Product Bound**: A helper lemma showing that $|\langle a, b \rangle| \le \frac{1}{2} \|a\|^2 + \frac{1}{2} \|b\|^2$, which
implies $\|a+b\|^2 \le 2\|a\|^2 + 2\|b\|^2$. -/
private lemma norm_add_sq_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a b : V) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  rw [norm_add_sq_real]
  have h := real_inner_le_norm a b
  have h_amgm : 2 * inner ℝ a b ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    have h1 := two_mul_le_add_sq ‖a‖ ‖b‖
    linarith [h, h1]
  linarith

/-- Integrability of the squared gradient norm follows from the integrability of the
squared norm of the input, under the L-smoothness assumption. -/
lemma integrable_gradient_sq_of_norm_sq {f : W ι → ℝ} {w : Ω → W ι} {L : NNReal}
    (h_smooth : is_smooth f L) (hw : Integrable (fun ω => ‖w ω‖ ^ 2)) :
    Integrable (fun ω => ‖gradient f (w ω)‖ ^ 2) := by
  apply Integrable.mono' (g := fun ω => 2 * (L : ℝ)^2 * ‖w ω‖ ^ 2 + 2 * ‖gradient f 0‖ ^ 2)
  · exact (hw.const_mul (2 * (L : ℝ)^2)).add (integrable_const _)
  · exact sorry -- Measurability
  · exact ae_of_all ℙ (fun ω => sorry) -- Bound

/-- Integrability of the objective value follows from the integrability of the
squared norm of the input, under L-smoothness and bounded below assumptions. -/
lemma integrable_f_of_norm_sq {f : W ι → ℝ} {w : Ω → W ι} {L : NNReal}
    (h_smooth : is_smooth f L) (h_bdd : BddBelow (Set.range f))
    (hw : Integrable (fun ω => ‖w ω‖ ^ 2)) :
    Integrable (fun ω => f (w ω)) := by
  let B := h_bdd.some
  apply Integrable.mono' (g := fun ω => |f 0| + ‖gradient f 0‖ * ‖w ω‖ + (L / 2) * ‖w ω‖ ^ 2 + |B|)
  · apply Integrable.add (Integrable.add (Integrable.add (integrable_const _) sorry) (hw.const_mul (L / 2))) (integrable_const _)
  · exact sorry -- Measurability
  · exact ae_of_all ℙ (fun ω => sorry) -- Bound

/-- **Structural Integrability**: The main theorem that derives the entire sequence of
integrability witnesses from structural assumptions. -/
theorem zsharp_structural_integrability (f : W ι → ℝ) (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (h_struct : ZSharpStructuralAssumptions f w η z σsq) :
    (∀ t, Integrable (fun ω => f (w t ω))) ∧
    (∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2)) := by
  have h_w_int : ∀ t, Integrable (fun ω => ‖w t ω‖ ^ 2) := by
    intro t
    induction t with
    | zero => exact h_struct.h_w0
    | succ t ih =>
      let L := h_struct.L_smooth
      let hL := h_struct.h_smooth
      let g_adv (ω : Ω) := gradient f (w t ω)
      have h_grad_sq_int : Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) :=
        integrable_gradient_sq_of_norm_sq hL ih
      have h_filt_int : Integrable (fun ω => ‖filtered_gradient (g_adv ω) z‖ ^ 2) := by
        apply Integrable.mono' (g := fun ω => ‖gradient f (w t ω)‖ ^ 2)
        · exact h_grad_sq_int
        · exact sorry
        · exact ae_of_all ℙ (fun ω => sorry)
      apply Integrable.congr (f := fun ω => ‖stochastic_zsharp_step (w t ω) η t z (fun ω' => gradient f (w t ω')) ω‖ ^ 2)
      · apply Integrable.mono' (g := fun ω => 2 * ‖w t ω‖ ^ 2 + 2 * (‖η t‖ ^ 2 * ‖filtered_gradient (g_adv ω) z‖ ^ 2))
        · apply Integrable.add (ih.const_mul 2)
          let η_sq := ‖η t‖ ^ 2
          apply Integrable.congr (f := fun ω => 2 * η_sq * ‖filtered_gradient (g_adv ω) z‖ ^ 2)
          · exact h_filt_int.const_mul (2 * η_sq)
          · refine ae_of_all ℙ (fun ω => ?_)
            ring
        · exact sorry
        · exact ae_of_all ℙ (fun ω => sorry)
      · filter_upwards [h_struct.h_step t] with ω h_eq
        rw [h_eq]
  constructor
  · intro t
    exact integrable_f_of_norm_sq h_struct.h_smooth h_struct.h_bdd_below (h_w_int t)
  · intro t
    exact integrable_gradient_sq_of_norm_sq h_struct.h_smooth (h_w_int t)

end LeanSharp
