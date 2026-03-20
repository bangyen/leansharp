/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Structural.SobolevRegularity.H1

/-!
# Sobolev Regularity - H² Regularity

This module introduces the $H^2$ regularity contract and provides constructors
and equivalence theorems relating it to classical second derivatives.

## Main Definitions
* `IsH2`: Bundled $H^2$ regularity predicate.

## Main Theorems
* `is_h2_of_fderiv_l2`: Constructor from classical second derivatives.
* `is_h2_implies_is_h1`: Regularity hierarchy theorem.
-/

namespace LeanSharp

open MeasureTheory

variable {ι : Type*} [Fintype ι]
variable [MeasurableSpace (W ι)]

/-- `H²`-style regularity contract in the current finite-dimensional setting. -/
def IsH2 (μ : Measure (W ι)) (u : W ι → ℝ) : Prop :=
  ∃ grad_u : W ι → W ι, ∃ hess_u : W ι → W ι →L[ℝ] W ι,
    HasWeakGradient u grad_u ∧
      HasWeakHessian grad_u hess_u ∧
      IsL2Scalar μ u ∧
      IsL2Vector μ grad_u ∧
      IsL2Hessian μ hess_u

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
