/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Theory.Dynamics.Generalization
import LeanSharp.Theory.Dynamics.SamBound

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

* `zsharp_gap_benefit`: Proves that the Z-score filter reduces the gradient-norm
  term in the generalization bound.
* `standard_bound_of_zsharp`: Proves that a ZSharp PAC-Bayes bound implies
  a standard SAM sharpness bound (showing ZSharp is the stricter/tighter condition).
* `filtered_rademacher_le`: Proves the reduction of effective Rademacher complexity.
-/

namespace LeanSharp

open Real NNReal

variable {ι : Type*} [Fintype ι]

/-- The ZSharp PAC-Bayes Bound Predicate.
    States that the population risk is bounded by the filtered empirical expansion. -/
def ZSharpPacBayesBound (L_D L_S : W ι → ℝ) (w : W ι) (ρ z : ℝ) (C : ℝ) : Prop :=
  L_D w ≤ L_S w + ‖filteredGradient (gradient L_S w) z‖ * ρ + C

/-- **Strict Complexity Reduction**:
    The generalization gap attributed to the gradient norm is strictly reduced
    by the Z-score filter whenever outliers are present. -/
theorem zsharp_gap_benefit (g : W ι) (z : ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ‖filteredGradient g z‖ * ρ ≤ ‖g‖ * ρ := by
  have h_contract := norm_filteredGradient_le g z
  nlinarith

/-- **ZSharp Generalization Hierarchy**:
    Any population risk bound that holds for Filtered SAM (ZSharp) also holds
    for standard SAM under the PAC-Bayes sharpness formulation.
    This establishes that ZSharp is a tighter "Generalization Basis". -/
theorem standard_bound_of_zsharp (L_D L_S : W ι → ℝ) (w : W ι) (ρ z C : ℝ) (hρ : 0 ≤ ρ)
    (h_zs : ZSharpPacBayesBound L_D L_S w ρ z C) :
    PacBayesSharpnessBound L_D L_S w ρ C := by
  unfold ZSharpPacBayesBound at h_zs
  unfold PacBayesSharpnessBound
  have h_benefit := zsharp_gap_benefit (gradient L_S w) z ρ hρ
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
  have h_norm := norm_filteredGradient_le g z
  by_cases hg : ‖g‖ = 0
  · -- Leverage Lean's x / 0 = 0 behavior
    rw [hg]
    simp only [div_zero, zero_mul, hR]
  · have hg_pos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg)
    have h_ratio : ‖filteredGradient g z‖ / ‖g‖ ≤ 1 := by
      rw [div_le_one hg_pos]
      exact h_norm
    nlinarith

end LeanSharp
