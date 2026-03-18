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

* `h1_interface_from_strong_data_test`.
* `h2_interface_from_strong_data_test`.
* `weak_gradient_transition_equivalence_test`.
* `weak_hessian_transition_equivalence_test`.
* `h1_transition_mapping_test`.
* `h2_transition_mapping_test`.
* `h2_implies_h1_interface_test`.
-/

namespace LeanSharp

open MeasureTheory

variable {ι : Type*} [Fintype ι]
variable [MeasurableSpace (W ι)]

/-- **H¹ Interface Verification**: strong differentiability plus `L²` assumptions
construct a valid `H¹` witness through `is_h1_of_strong_data`. -/
theorem h1_interface_from_strong_data_test
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_fderiv : ∀ x, HasFDerivAt u (fderiv ℝ u x) x)
    (h_l2_u : is_l2_scalar μ u)
    (h_l2_grad : is_l2_vector μ (gradient u)) :
    is_h1 μ u := by
  exact is_h1_of_strong_data μ u h_fderiv h_l2_u h_l2_grad

/-- **H² Interface Verification**: strong first/second differentiability plus
`L²` assumptions construct a valid `H²` witness. -/
theorem h2_interface_from_strong_data_test
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_fderiv : ∀ x, HasFDerivAt u (fderiv ℝ u x) x)
    (h_grad_fderiv : ∀ x, HasFDerivAt (gradient u) (fderiv ℝ (gradient u) x) x)
    (h_l2_u : is_l2_scalar μ u)
    (h_l2_grad : is_l2_vector μ (gradient u))
    (h_l2_hess : is_l2_hessian μ (hessian u)) :
    is_h2 μ u := by
  exact is_h2_of_strong_data μ u h_fderiv h_grad_fderiv h_l2_u h_l2_grad h_l2_hess

omit [MeasurableSpace (W ι)] in
/-- **Weak-Gradient Transition Equivalence Verification**: checks the explicit
equivalence between weak-gradient and standard Fréchet derivative data when the
weak field is chosen as `gradient u`. -/
theorem weak_gradient_transition_equivalence_test
    (u : W ι → ℝ) :
    has_weak_gradient u (gradient u) ↔
      (∀ x, HasFDerivAt u (fderiv ℝ u x) x) := by
  exact has_weak_gradient_with_gradient_iff_fderiv u

omit [MeasurableSpace (W ι)] in
/-- **Weak-Hessian Transition Equivalence Verification**: checks the explicit
equivalence between weak-Hessian and standard derivative data for `gradient u`
when the weak field is chosen as `hessian u`. -/
theorem weak_hessian_transition_equivalence_test
    (u : W ι → ℝ) :
    has_weak_hessian (gradient u) (hessian u) ↔
      (∀ x, HasFDerivAt (gradient u) (fderiv ℝ (gradient u) x) x) := by
  exact has_weak_hessian_with_hessian_iff_gradient_fderiv u

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
