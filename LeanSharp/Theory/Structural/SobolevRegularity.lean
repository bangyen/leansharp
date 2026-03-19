/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import LeanSharp.Core.Taylor.SamBounds
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Sobolev Regularity Interfaces

This module introduces lightweight `H¹`/`H²`-style regularity predicates in the
current finite-dimensional parameter-space setting. It exists to provide explicit
contracts for weak-derivative style assumptions before full functional-analysis
generalization.

## Definitions

* `IsL2Scalar`.
* `IsL2Vector`.
* `IsL2Hessian`.
* `HasWeakGradient`.
* `HasWeakHessian`.
* `IsH1`.
* `IsH2`.

## Theorems

* `has_weak_gradient_of_fderiv`.
* `has_weak_hessian_of_gradient_fderiv`.
* `is_h1_with_gradient_iff`.
* `is_h2_with_gradient_hessian_iff`.
* `is_h1_of_fderiv_l2`.
* `is_h2_of_fderiv_l2`.
* `exists_weak_gradient_data_of_is_h1`.
* `exists_weak_hessian_data_of_is_h2`.
* `is_h2_implies_is_h1`.
-/

namespace LeanSharp

open MeasureTheory

variable {ι : Type*} [Fintype ι]
variable [MeasurableSpace (W ι)]

/-- `L²` regularity for scalar-valued functions on parameter space. -/
def IsL2Scalar (μ : Measure (W ι)) (u : W ι → ℝ) : Prop :=
  Integrable (fun x => ‖u x‖ ^ 2) μ

/-- `L²` regularity for vector-valued fields on parameter space. -/
def IsL2Vector (μ : Measure (W ι)) (v : W ι → W ι) : Prop :=
  Integrable (fun x => ‖v x‖ ^ 2) μ

/-- `L²` regularity for Hessian fields on parameter space. -/
def IsL2Hessian (μ : Measure (W ι)) (h : W ι → W ι →L[ℝ] W ι) : Prop :=
  Integrable (fun x => ‖h x‖ ^ 2) μ

/-- Weak-gradient interface contract: the provided field reproduces the Fréchet
derivative through the Riesz map at every point. -/
def HasWeakGradient (u : W ι → ℝ) (grad_u : W ι → W ι) : Prop :=
  ∀ x, HasFDerivAt u ((InnerProductSpace.toDual ℝ (W ι)) (grad_u x)) x

/-- Weak-Hessian interface contract: the provided Hessian field is the derivative
of the weak-gradient field at every point. -/
def HasWeakHessian (grad_u : W ι → W ι) (hess_u : W ι → W ι →L[ℝ] W ι) : Prop :=
  ∀ x, HasFDerivAt grad_u (hess_u x) x

/-- `H¹`-style regularity contract in the current finite-dimensional setting. -/
def IsH1 (μ : Measure (W ι)) (u : W ι → ℝ) : Prop :=
  ∃ grad_u : W ι → W ι,
    HasWeakGradient u grad_u ∧
      IsL2Scalar μ u ∧
      IsL2Vector μ grad_u

/-- `H²`-style regularity contract in the current finite-dimensional setting. -/
def IsH2 (μ : Measure (W ι)) (u : W ι → ℝ) : Prop :=
  ∃ grad_u : W ι → W ι, ∃ hess_u : W ι → W ι →L[ℝ] W ι,
    HasWeakGradient u grad_u ∧
      HasWeakHessian grad_u hess_u ∧
      IsL2Scalar μ u ∧
      IsL2Vector μ grad_u ∧
      IsL2Hessian μ hess_u

omit [MeasurableSpace (W ι)] in
/-- **Interface corollary**: strong differentiability data yields the weak-gradient
contract by choosing the existing `gradient` field from `Core/Landscape`. -/
theorem has_weak_gradient_of_fderiv
    (u : W ι → ℝ)
    (h_fderiv : ∀ x, HasFDerivAt u (fderiv ℝ u x) x) :
    HasWeakGradient u (gradient u) := by
  intro x
  simpa only [
    gradient,
    LinearIsometryEquiv.apply_symm_apply
  ] using h_fderiv x

omit [MeasurableSpace (W ι)] in
/-- **Interface corollary**: strong differentiability data for `gradient u`
yields the weak-Hessian contract by choosing the existing `hessian` field from
`Core/Landscape`. -/
theorem has_weak_hessian_of_gradient_fderiv
    (u : W ι → ℝ)
    (h_grad_fderiv : ∀ x, HasFDerivAt (gradient u) (fderiv ℝ (gradient u) x) x) :
    HasWeakHessian (gradient u) (hessian u) := by
  intro x
  simpa only [hessian] using h_grad_fderiv x

/-- **Interface equivalence** for the `gradient` choice: this maps the bundled
`H¹` contract to standard derivative plus `L²` data, and back. -/
theorem is_h1_with_gradient_iff
    (μ : Measure (W ι)) (u : W ι → ℝ) :
    (HasWeakGradient u (gradient u) ∧ IsL2Scalar μ u ∧ IsL2Vector μ (gradient u))
      ↔ ((∀ x, HasFDerivAt u (fderiv ℝ u x) x) ∧
        IsL2Scalar μ u ∧ IsL2Vector μ (gradient u)) := by
  constructor
  · intro h
    refine ⟨fun x => ?_, h.2.1, h.2.2⟩
    have hx := h.1 x
    simpa only [gradient, LinearIsometryEquiv.apply_symm_apply] using hx
  · intro h
    refine ⟨has_weak_gradient_of_fderiv u h.1, h.2.1, h.2.2⟩

/-- **Interface equivalence** for the `gradient`/`hessian` choice: this bridges
bundled weak contracts and standard first/second derivative data with matching
`L²` assumptions. -/
theorem is_h2_with_gradient_hessian_iff
    (μ : Measure (W ι)) (u : W ι → ℝ) :
    (HasWeakGradient u (gradient u) ∧
      HasWeakHessian (gradient u) (hessian u) ∧
      IsL2Scalar μ u ∧
      IsL2Vector μ (gradient u) ∧
      IsL2Hessian μ (hessian u))
      ↔
      (∀ x, HasFDerivAt u (fderiv ℝ u x) x) ∧
      (∀ x, HasFDerivAt (gradient u) (fderiv ℝ (gradient u) x) x) ∧
      IsL2Scalar μ u ∧
      IsL2Vector μ (gradient u) ∧
      IsL2Hessian μ (hessian u) := by
  constructor
  · intro h
    refine ⟨?_, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    · intro x
      have hx := h.1 x
      simpa only [gradient, LinearIsometryEquiv.apply_symm_apply] using hx
    · intro x
      have hx := h.2.1 x
      simpa only [hessian] using hx
  · intro h
    refine ⟨
      has_weak_gradient_of_fderiv u h.1,
      has_weak_hessian_of_gradient_fderiv u h.2.1,
      h.2.2.1,
      h.2.2.2.1,
      h.2.2.2.2
    ⟩

/-- **Classical-to-`H¹` constructor**: packages classical derivative data with
`L²` assumptions into the existential `IsH1` contract. This exists so theorem
clients can transition from standard differentiability assumptions to bundled
weak-regularity hypotheses in one step. -/
theorem is_h1_of_fderiv_l2
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_fderiv : ∀ x, HasFDerivAt u (fderiv ℝ u x) x)
    (h_l2_u : IsL2Scalar μ u)
    (h_l2_grad : IsL2Vector μ (gradient u)) :
    IsH1 μ u := by
  exact ⟨gradient u, has_weak_gradient_of_fderiv u h_fderiv, h_l2_u, h_l2_grad⟩

/-- **Classical-to-`H²` constructor**: packages first/second derivative data
with `L²` assumptions into the existential `IsH2` contract. This exists to
support downstream results that consume weak-regularity bundles while proofs are
stated using standard derivatives. -/
theorem is_h2_of_fderiv_l2
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_fderiv : ∀ x, HasFDerivAt u (fderiv ℝ u x) x)
    (h_grad_fderiv : ∀ x, HasFDerivAt (gradient u) (fderiv ℝ (gradient u) x) x)
    (h_l2_u : IsL2Scalar μ u)
    (h_l2_grad : IsL2Vector μ (gradient u))
    (h_l2_hess : IsL2Hessian μ (hessian u)) :
    IsH2 μ u := by
  exact ⟨
    gradient u,
    hessian u,
    has_weak_gradient_of_fderiv u h_fderiv,
    has_weak_hessian_of_gradient_fderiv u h_grad_fderiv,
    h_l2_u,
    h_l2_grad,
    h_l2_hess
  ⟩

/-- **`H¹` witness extraction**: unfolds the existential `IsH1` contract into a
reusable weak-gradient witness and `L²` certificates for downstream theorems. -/
theorem exists_weak_gradient_data_of_is_h1
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_h1 : IsH1 μ u) :
    ∃ grad_u : W ι → W ι,
      HasWeakGradient u grad_u ∧ IsL2Scalar μ u ∧ IsL2Vector μ grad_u := by
  simpa only [IsH1] using h_h1

/-- **`H²` witness extraction**: unfolds the existential `IsH2` contract into
weak-gradient/weak-Hessian witnesses and `L²` certificates. This exists to make
`IsH2` assumptions directly consumable by higher-order descent lemmas. -/
theorem exists_weak_hessian_data_of_is_h2
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_h2 : IsH2 μ u) :
    ∃ grad_u : W ι → W ι, ∃ hess_u : W ι → W ι →L[ℝ] W ι,
      HasWeakGradient u grad_u ∧
        HasWeakHessian grad_u hess_u ∧
        IsL2Scalar μ u ∧
        IsL2Vector μ grad_u ∧
        IsL2Hessian μ hess_u := by
  simpa only [IsH2] using h_h2

/-- `H²` regularity implies `H¹` regularity by forgetting the Hessian field. -/
theorem is_h2_implies_is_h1
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_h2 : IsH2 μ u) :
    IsH1 μ u := by
  rcases h_h2 with ⟨grad_u, _, h_weak_grad, _, h_l2_u, h_l2_grad, _⟩
  exact ⟨grad_u, h_weak_grad, h_l2_u, h_l2_grad⟩

end LeanSharp
