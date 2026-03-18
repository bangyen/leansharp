/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Sobolev Regularity Interfaces

This module introduces lightweight `H¹`/`H²`-style regularity predicates in the
current finite-dimensional parameter-space setting. It exists to provide explicit
contracts for weak-derivative style assumptions before full functional-analysis
generalization.

## Definitions

* `is_l2_scalar`.
* `is_l2_vector`.
* `is_l2_hessian`.
* `has_weak_gradient`.
* `has_weak_hessian`.
* `is_h1`.
* `is_h2`.

## Theorems

* `has_weak_gradient_of_fderiv`.
* `has_weak_hessian_of_gradient_fderiv`.
* `has_weak_gradient_with_gradient_iff_fderiv`.
* `has_weak_hessian_with_hessian_iff_gradient_fderiv`.
* `is_h1_with_gradient_iff`.
* `is_h2_with_gradient_hessian_iff`.
* `is_h1_of_strong_data`.
* `is_h2_of_strong_data`.
* `is_h2_implies_is_h1`.
-/

namespace LeanSharp

open MeasureTheory

variable {ι : Type*} [Fintype ι]
variable [MeasurableSpace (W ι)]

/-- `L²` regularity for scalar-valued functions on parameter space. -/
def is_l2_scalar (μ : Measure (W ι)) (u : W ι → ℝ) : Prop :=
  Integrable (fun x => ‖u x‖ ^ 2) μ

/-- `L²` regularity for vector-valued fields on parameter space. -/
def is_l2_vector (μ : Measure (W ι)) (v : W ι → W ι) : Prop :=
  Integrable (fun x => ‖v x‖ ^ 2) μ

/-- `L²` regularity for Hessian fields on parameter space. -/
def is_l2_hessian (μ : Measure (W ι)) (h : W ι → W ι →L[ℝ] W ι) : Prop :=
  Integrable (fun x => ‖h x‖ ^ 2) μ

/-- Weak-gradient interface contract: the provided field reproduces the Fréchet
derivative through the Riesz map at every point. -/
def has_weak_gradient (u : W ι → ℝ) (grad_u : W ι → W ι) : Prop :=
  ∀ x, HasFDerivAt u ((InnerProductSpace.toDual ℝ (W ι)) (grad_u x)) x

/-- Weak-Hessian interface contract: the provided Hessian field is the derivative
of the weak-gradient field at every point. -/
def has_weak_hessian (grad_u : W ι → W ι) (hess_u : W ι → W ι →L[ℝ] W ι) : Prop :=
  ∀ x, HasFDerivAt grad_u (hess_u x) x

/-- `H¹`-style regularity contract in the current finite-dimensional setting. -/
def is_h1 (μ : Measure (W ι)) (u : W ι → ℝ) : Prop :=
  ∃ grad_u : W ι → W ι,
    has_weak_gradient u grad_u ∧
      is_l2_scalar μ u ∧
      is_l2_vector μ grad_u

/-- `H²`-style regularity contract in the current finite-dimensional setting. -/
def is_h2 (μ : Measure (W ι)) (u : W ι → ℝ) : Prop :=
  ∃ grad_u : W ι → W ι, ∃ hess_u : W ι → W ι →L[ℝ] W ι,
    has_weak_gradient u grad_u ∧
      has_weak_hessian grad_u hess_u ∧
      is_l2_scalar μ u ∧
      is_l2_vector μ grad_u ∧
      is_l2_hessian μ hess_u

omit [MeasurableSpace (W ι)] in
/-- Strong differentiability data yields the weak-gradient interface by choosing
the existing `gradient` field from `Core/Landscape`. -/
theorem has_weak_gradient_of_fderiv
    (u : W ι → ℝ)
    (h_fderiv : ∀ x, HasFDerivAt u (fderiv ℝ u x) x) :
    has_weak_gradient u (gradient u) := by
  intro x
  simpa only [
    gradient,
    LinearIsometryEquiv.apply_symm_apply
  ] using h_fderiv x

omit [MeasurableSpace (W ι)] in
/-- Strong differentiability data for `gradient u` yields the weak-Hessian
interface by choosing the existing `hessian` field from `Core/Landscape`. -/
theorem has_weak_hessian_of_gradient_fderiv
    (u : W ι → ℝ)
    (h_grad_fderiv : ∀ x, HasFDerivAt (gradient u) (fderiv ℝ (gradient u) x) x) :
    has_weak_hessian (gradient u) (hessian u) := by
  intro x
  simpa only [hessian] using h_grad_fderiv x

omit [MeasurableSpace (W ι)] in
/-- Transition equivalence between the weak-gradient contract instantiated with
`gradient u` and standard Fréchet derivative data for `u`. -/
theorem has_weak_gradient_with_gradient_iff_fderiv
    (u : W ι → ℝ) :
    has_weak_gradient u (gradient u) ↔
      (∀ x, HasFDerivAt u (fderiv ℝ u x) x) := by
  constructor
  · intro h x
    have hx := h x
    simpa only [gradient, LinearIsometryEquiv.apply_symm_apply] using hx
  · intro h
    exact has_weak_gradient_of_fderiv u h

omit [MeasurableSpace (W ι)] in
/-- Transition equivalence between the weak-Hessian contract instantiated with
`hessian u` and standard derivative data for `gradient u`. -/
theorem has_weak_hessian_with_hessian_iff_gradient_fderiv
    (u : W ι → ℝ) :
    has_weak_hessian (gradient u) (hessian u) ↔
      (∀ x, HasFDerivAt (gradient u) (fderiv ℝ (gradient u) x) x) := by
  constructor
  · intro h x
    have hx := h x
    simpa only [hessian] using hx
  · intro h
    exact has_weak_hessian_of_gradient_fderiv u h

/-- Explicit `H¹` transition mapping when the weak field is chosen as `gradient u`.
This theorem gives a direct equivalence between the bundled `H¹` contract and
the corresponding standard-derivative plus `L²` data. -/
theorem is_h1_with_gradient_iff
    (μ : Measure (W ι)) (u : W ι → ℝ) :
    (has_weak_gradient u (gradient u) ∧ is_l2_scalar μ u ∧ is_l2_vector μ (gradient u))
      ↔ (∀ x, HasFDerivAt u (fderiv ℝ u x) x) ∧ is_l2_scalar μ u ∧ is_l2_vector μ (gradient u) := by
  constructor
  · intro h
    refine ⟨(has_weak_gradient_with_gradient_iff_fderiv u).1 h.1, h.2.1, h.2.2⟩
  · intro h
    refine ⟨(has_weak_gradient_with_gradient_iff_fderiv u).2 h.1, h.2.1, h.2.2⟩

/-- Explicit `H²` transition mapping when weak fields are chosen as
`gradient u` and `hessian u`. This theorem bridges bundled weak contracts and
standard first/second derivative data with matching `L²` assumptions. -/
theorem is_h2_with_gradient_hessian_iff
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
  constructor
  · intro h
    refine ⟨
      (has_weak_gradient_with_gradient_iff_fderiv u).1 h.1,
      (has_weak_hessian_with_hessian_iff_gradient_fderiv u).1 h.2.1,
      h.2.2.1,
      h.2.2.2.1,
      h.2.2.2.2
    ⟩
  · intro h
    refine ⟨
      (has_weak_gradient_with_gradient_iff_fderiv u).2 h.1,
      (has_weak_hessian_with_hessian_iff_gradient_fderiv u).2 h.2.1,
      h.2.2.1,
      h.2.2.2.1,
      h.2.2.2.2
    ⟩

/-- Bundles strong differentiability and `L²` assumptions into an `H¹` witness. -/
theorem is_h1_of_strong_data
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_fderiv : ∀ x, HasFDerivAt u (fderiv ℝ u x) x)
    (h_l2_u : is_l2_scalar μ u)
    (h_l2_grad : is_l2_vector μ (gradient u)) :
    is_h1 μ u := by
  refine ⟨gradient u, has_weak_gradient_of_fderiv u h_fderiv, h_l2_u, h_l2_grad⟩

/-- Bundles strong differentiability and `L²` assumptions into an `H²` witness. -/
theorem is_h2_of_strong_data
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_fderiv : ∀ x, HasFDerivAt u (fderiv ℝ u x) x)
    (h_grad_fderiv : ∀ x, HasFDerivAt (gradient u) (fderiv ℝ (gradient u) x) x)
    (h_l2_u : is_l2_scalar μ u)
    (h_l2_grad : is_l2_vector μ (gradient u))
    (h_l2_hess : is_l2_hessian μ (hessian u)) :
    is_h2 μ u := by
  refine ⟨gradient u, hessian u, ?_, ?_, h_l2_u, h_l2_grad, h_l2_hess⟩
  · exact has_weak_gradient_of_fderiv u h_fderiv
  · exact has_weak_hessian_of_gradient_fderiv u h_grad_fderiv

/-- `H²` regularity implies `H¹` regularity by forgetting the Hessian field. -/
theorem is_h2_implies_is_h1
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_h2 : is_h2 μ u) :
    is_h1 μ u := by
  rcases h_h2 with ⟨grad_u, hess_u, h_weak_grad, h_weak_hess, h_l2_u, h_l2_grad, h_l2_hess⟩
  exact ⟨grad_u, h_weak_grad, h_l2_u, h_l2_grad⟩

end LeanSharp
