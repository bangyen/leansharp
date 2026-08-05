/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Theory.Robustness.PacBayes

/-!
# PAC-Bayes Tests

This module instantiates the ZSharp PAC-Bayes bound on the quadratic-bowl
landscape: the pointwise bound holds for the toy loss itself, and both the
standard-SAM comparison and the distributional integration fire on the concrete
example.

## Examples

* `quadratic_bowl_zsharp_bound_holds`.
* `quadratic_bowl_zsharp_implies_standard`.
* `quadratic_bowl_zsharp_distributional`.
-/

namespace LeanSharp.Tests

open LeanSharp.QuadraticBowl
open MeasureTheory

local notation "W2" => W (Fin 2)

/-- The ZSharp PAC-Bayes bound holds for the toy loss against itself with $C = 0$:
the population risk is (vacuously) bounded by the filtered expansion since the
filter term is non-negative. -/
example (w : W2) (ρ z : ℝ) (hρ : 0 ≤ ρ) :
    ZSharpPacBayesBound toyLoss toyLoss w ρ z 0 := by
  unfold ZSharpPacBayesBound
  have h_nonneg : 0 ≤ ‖filteredGradient (gradient toyLoss w) z‖ * ρ :=
    mul_nonneg (norm_nonneg _) hρ
  linarith

/-- The fully-evaluated pointwise bound: substituting the analytical gradient
`∇toyLoss = exactGradientToy` into the filtered expansion. -/
example (w : W2) (ρ z : ℝ) (hρ : 0 ≤ ρ) :
    toyLoss w ≤ toyLoss w + ‖filteredGradient (exactGradientToy w) z‖ * ρ := by
  rw [← gradient_toy_eq]
  have h_nonneg : 0 ≤ ‖filteredGradient (gradient toyLoss w) z‖ * ρ :=
    mul_nonneg (norm_nonneg _) hρ
  linarith

/-- The ZSharp-to-standard-SAM comparison specializes to the quadratic bowl. -/
example (L_D : W2 → ℝ) (w : W2) (ρ z C : ℝ) (hρ : 0 ≤ ρ)
    (h_zs : ZSharpPacBayesBound L_D toyLoss w ρ z C) :
    PacBayesSharpnessBound L_D toyLoss w ρ C := by
  exact standard_bound_of_z_sharp L_D toyLoss w ρ z C hρ h_zs

/-- The pointwise-to-distributional PAC-Bayes step specializes to the quadratic bowl. -/
example (L_D : W2 → ℝ) (P : Measure W2) [IsProbabilityMeasure P] (ρ z C : ℝ)
    (h : ∀ w, ZSharpPacBayesBound L_D toyLoss w ρ z C)
    (h_D : Integrable L_D P)
    (h_S : Integrable toyLoss P)
    (h_f : Integrable (fun w => ‖filteredGradient (gradient toyLoss w) z‖ * ρ) P) :
    ∫ w, L_D w ∂P ≤ ∫ w, toyLoss w ∂P +
        ∫ w, ‖filteredGradient (gradient toyLoss w) z‖ * ρ ∂P + C := by
  exact z_sharp_pac_bayes_expected P ρ z C h h_D h_S h_f

end LeanSharp.Tests
