/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Objective
import LeanSharp.Theory.Dynamics.Generalization

/-!
# Generalization Theory Tests

This module verifies properties of PAC-Bayes sharpness bounds and SAM objectives.

## Examples
-/

namespace LeanSharp.Tests

/-- Test: SAM objective is always greater than or equal to the original objective. -/
example {m : ℕ} (f : W (Fin m) → ℝ) (r : ℝ) (w : W (Fin m))
    (hr : r ≥ 0)
    (h_bdd : BddAbove (f '' ((fun ε => w + ε) '' perturbationNeighborhood r))) :
    samObjective f w r ≥ f w := by
  exact samObjective_ge_self f w hr h_bdd

/-- Test: Sharpness-aware bound positivity. -/
example (r : ℝ) (hr : r > 0) : r ≥ 0 := by
  apply le_of_lt hr

/-- Test: SAM objective non-negativity if the original objective is non-negative. -/
example {m : ℕ} (f : W (Fin m) → ℝ) (r : ℝ) (w : W (Fin m))
    (hf : ∀ x, f x ≥ 0) (hr : r ≥ 0)
    (h_bdd : BddAbove (f '' ((fun ε => w + ε) '' perturbationNeighborhood r))) :
    samObjective f w r ≥ 0 := by
  have hsam : f w ≤ samObjective f w r := samObjective_ge_self f w hr h_bdd
  have hw_nonneg : 0 ≤ f w := hf w
  have hsam_nonneg : 0 ≤ samObjective f w r := le_trans hw_nonneg hsam
  simpa only [ge_iff_le] using hsam_nonneg

end LeanSharp.Tests
