/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Theory.SobolevRegularity

/-!
# Sobolev Regularity Interface Tests

This module verifies that `H¹`/`H²` interface theorems compose correctly in
downstream statements.

## Theorems

* `h1_transition_mapping_test`.
* `h2_transition_mapping_test`.
* `h2_implies_h1_interface_test`.
-/

namespace LeanSharp

open MeasureTheory

variable {ι : Type*} [Fintype ι]
variable [MeasurableSpace (W ι)]

/-- **H¹ Transition Mapping Verification**: checks the direct transition mapping
between bundled weak-contract `H¹` data and standard derivative data. -/
theorem h1_transition_mapping_test
    (μ : Measure (W ι)) (u : W ι → ℝ) :
    (has_weak_gradient u (gradient u) ∧ is_l2_scalar μ u ∧ is_l2_vector μ (gradient u))
      ↔ (∀ x, HasFDerivAt u (fderiv ℝ u x) x) ∧ is_l2_scalar μ u ∧ is_l2_vector μ (gradient u) := by
  exact is_h1_with_gradient_iff μ u

/-- **H² Transition Mapping Verification**: checks the direct transition mapping
between bundled weak-contract `H²` data and standard first/second derivative
data with matching `L²` assumptions. -/
theorem h2_transition_mapping_test
    (μ : Measure (W ι)) (u : W ι → ℝ) :
    (has_weak_gradient u (gradient u) ∧
      has_weak_hessian (gradient u) (hessian u) ∧
      is_l2_scalar μ u ∧
      is_l2_vector μ (gradient u) ∧
      is_l2_hessian μ (hessian u))
      ↔
      (∀ x, HasFDerivAt u (fderiv ℝ u x) x) ∧
      (∀ x, HasFDerivAt (gradient u) (fderiv ℝ (gradient u) x) x) ∧
      is_l2_scalar μ u ∧
      is_l2_vector μ (gradient u) ∧
      is_l2_hessian μ (hessian u) := by
  exact is_h2_with_gradient_hessian_iff μ u

/-- **H²-to-H¹ Projection Verification**: checks that the interface projection
from `H²` to `H¹` is available to downstream users. -/
theorem h2_implies_h1_interface_test
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_h2 : is_h2 μ u) :
    is_h1 μ u := by
  exact is_h2_implies_is_h1 μ u h_h2

end LeanSharp
