/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.Filters
import LeanSharp.Theory.Dynamics.Convergence

/-!
# ZSharp Perturbation Tests

This module exists to verify that the paper-faithful ZSharp ascent step
(arXiv:2505.02369), which is computed from the *filtered* gradient rather than
the raw one, satisfies the radius bound and degenerates to the ordinary SAM
perturbation exactly in the paper's fallback case.

## Examples

* `test_norm_zsharpPerturbation_le_interface`.
* `test_zsharpPerturbation_fallback_interface`.
* `test_zsharpPerturbation_eq_filtered_direction`.
* `test_zsharpStep_uses_filtered_perturbation`.
-/

namespace LeanSharp.Tests

variable {ι : Type*} [Fintype ι]

/-- Interface test: the ZSharp perturbation stays inside the radius-`ρ` ball,
matching the guarantee the SAM perturbation provides. -/
example (L : W ι → ℝ) (w : W ι) (ρ z : ℝ) (hρ : 0 ≤ ρ) :
    ‖zsharpPerturbation L w ρ z‖ ≤ ρ :=
  norm_zsharpPerturbation_le L w ρ z hρ

/-- Interface test: when the Z-score filter annihilates the gradient, the ZSharp
perturbation falls back to the ordinary SAM perturbation, as in the paper's
second case. -/
example (L : W ι → ℝ) (w : W ι) (ρ z : ℝ)
    (h_zero : ‖filteredGradient (gradient L w) z‖ = 0) :
    zsharpPerturbation L w ρ z = samPerturbation L w ρ :=
  zsharpPerturbation_eq_samPerturbation_of_filtered_zero L w ρ z h_zero

/-- In the non-degenerate case the ascent step points along the *filtered*
gradient, which is the substance of the paper's definition: filtering steers the
perturbation direction rather than only rescaling the post-perturbation gradient. -/
example (L : W ι → ℝ) (w : W ι) (ρ z : ℝ)
    (h_pos : ‖filteredGradient (gradient L w) z‖ ≠ 0) :
    zsharpPerturbation L w ρ z =
      (ρ / ‖filteredGradient (gradient L w) z‖) • filteredGradient (gradient L w) z := by
  simp only [zsharpPerturbation, h_pos, ite_false]

/-- The ZSharp update step evaluates the gradient at the point displaced by the
filtered-gradient ascent step. -/
example (L : W ι → ℝ) (w : W ι) (η : ℕ → ℝ) (t : ℕ) (ρ z : ℝ) :
    zsharpStep L w η t ρ z =
      w - (η t) • filteredGradient (gradient L (w + zsharpPerturbation L w ρ z)) z :=
  rfl

end LeanSharp.Tests
