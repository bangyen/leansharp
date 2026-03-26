/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Theory.Dynamics.Generalization
import LeanSharp.Theory.Dynamics.SamBound
import LeanSharp.Theory.Robustness.PacBayesBasis
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# PAC-Bayes & Rademacher Complexity for Filtered SAM

This module formalizes the generalization benefits of Z-score gradient filtering.
We establish that filtering outliers acts as a structural regularizer that
reduces the effective complexity of the hypothesis class.

## Main definitions

* `ZSharpPacBayesBound`: A predicate for the generalization bound
  of a filtered objective in the Taylor regime.
* `FilteredRademacherComplexity`: The Rademacher complexity of the filtered
  gradient space.

## Main theorems

* `z_sharp_gap_benefit`: Proves that the Z-score filter reduces the gradient-norm
  term in the generalization bound.
* `standard_bound_of_z_sharp`: Proves that a ZSharp PAC-Bayes bound implies
  a standard SAM sharpness bound (showing ZSharp is the stricter/tighter condition).
* `filtered_rademacher_le`: Proves the reduction of effective Rademacher complexity.
* `z_sharp_pac_bayes_expected`: Proves that pointwise ZSharp bounds integrate
  to a distributional bound compatible with `PacBayesGeneralizationBound`.
-/

namespace LeanSharp

open MeasureTheory Real NNReal

variable {ι : Type*} [Fintype ι]

/-- The ZSharp PAC-Bayes Bound Predicate.
    States that the population risk is bounded by the filtered empirical expansion. -/
def ZSharpPacBayesBound (L_D L_S : W ι → ℝ) (w : W ι) (ρ z : ℝ) (C : ℝ) : Prop :=
  L_D w ≤ L_S w + ‖filteredGradient (gradient L_S w) z‖ * ρ + C

/-- **ZSharp Generalization Hierarchy**:
    Any population risk bound that holds for Filtered SAM (ZSharp) also holds
    for standard SAM under the PAC-Bayes sharpness formulation.
    This establishes that ZSharp is a tighter "Generalization Basis". -/
theorem standard_bound_of_z_sharp (L_D L_S : W ι → ℝ) (w : W ι) (ρ z C : ℝ) (hρ : 0 ≤ ρ)
    (h_zs : ZSharpPacBayesBound L_D L_S w ρ z C) :
    PacBayesSharpnessBound L_D L_S w ρ C := by
  unfold ZSharpPacBayesBound at h_zs
  unfold PacBayesSharpnessBound
  have h_benefit := z_sharp_gap_benefit (gradient L_S w) z ρ hρ
  linarith

/-- **Filtered Rademacher Complexity**:
    The Rademacher complexity of a function class $\mathcal{F}$ scaled by the
    Z-score filter contraction. -/
noncomputable def FilteredRademacherComplexity (R_base : ℝ) (g : W ι) (z : ℝ) : ℝ :=
  (‖filteredGradient g z‖ / ‖g‖) * R_base

/-- **Complexity Reduction Lemma**:
    The filtered Rademacher complexity is always no greater than the base
    Rademacher complexity. -/
theorem filtered_rademacher_le (R_base : ℝ) (g : W ι) (z : ℝ) (hR : 0 ≤ R_base) :
    FilteredRademacherComplexity R_base g z ≤ R_base := by
  unfold FilteredRademacherComplexity
  have h_norm := norm_filtered_gradient_le g z
  by_cases hg : ‖g‖ = 0
  · -- Leverage Lean's x / 0 = 0 behavior
    rw [hg]
    simp only [div_zero, zero_mul, hR]
  · have hg_pos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg)
    have h_ratio : ‖filteredGradient g z‖ / ‖g‖ ≤ 1 := by
      rw [div_le_one hg_pos]
      exact h_norm
    nlinarith

/-- **ZSharp to Distributional PAC-Bayes**:
    A pointwise `ZSharpPacBayesBound` integrates to an expected-risk inequality
    under any probability measure `P`, establishing `ZSharpPacBayesBound` as a
    pointwise special case of `PacBayesGeneralizationBound`. -/
theorem z_sharp_pac_bayes_expected {L_D L_S : W ι → ℝ} (P : Measure (W ι))
    [hP : IsProbabilityMeasure P] (ρ z C : ℝ)
    (h : ∀ w, ZSharpPacBayesBound L_D L_S w ρ z C)
    (h_D : Integrable L_D P)
    (h_S : Integrable L_S P)
    (h_f : Integrable (fun w => ‖filteredGradient (gradient L_S w) z‖ * ρ) P) :
    ∫ w, L_D w ∂P ≤ ∫ w, L_S w ∂P +
        ∫ w, ‖filteredGradient (gradient L_S w) z‖ * ρ ∂P + C := by
  have h_ae : ∀ᵐ w ∂P, L_D w ≤
      L_S w + ‖filteredGradient (gradient L_S w) z‖ * ρ + C :=
    Filter.Eventually.of_forall h
  have h_bnd := integral_mono_ae h_D
    (h_S.add h_f |>.add (integrable_const C)) h_ae
  have h_bnd' : ∫ w, L_D w ∂P ≤ ∫ w, L_S w ∂P +
      ∫ w, ‖filteredGradient (gradient L_S w) z‖ * ρ ∂P + C := by
    have h1 := integral_add (h_S.add h_f) (integrable_const C) (μ := P)
    have h2 := integral_add h_S h_f (μ := P)
    simp only [integral_const, probReal_univ, one_smul] at h1
    have h3 : ∫ a, (L_S + fun w => ‖filteredGradient (gradient L_S w) z‖ * ρ) a ∂P =
        ∫ a, L_S a ∂P + ∫ a, ‖filteredGradient (gradient L_S a) z‖ * ρ ∂P := h2
    have h_bnd2 : ∫ x, L_D x ∂P ≤
        ∫ a, (L_S a + ‖filteredGradient (gradient L_S a) z‖ * ρ) + C ∂P := h_bnd
    have h4 : ∫ a, (L_S a + ‖filteredGradient (gradient L_S a) z‖ * ρ) + C ∂P =
        ∫ a, (L_S + fun w => ‖filteredGradient (gradient L_S w) z‖ * ρ) a + C ∂P := rfl
    linarith [h_bnd2, h4 ▸ h_bnd2, h1, h3]
  exact h_bnd'

end LeanSharp
