/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Structural.SobolevRegularity.Basic

/-!
# Sobolev Regularity - H¹ Regularity

This module introduces the $H^1$ regularity contract and provides constructors
and equivalence theorems relating it to classical derivatives.

## Main Definitions
* `IsH1`: Bundled $H^1$ regularity predicate.

## Main Theorems
* `is_h1_of_fderiv_l2`: Constructor from classical derivatives.
-/

namespace LeanSharp

open MeasureTheory

variable {ι : Type*} [Fintype ι]
variable [MeasurableSpace (W ι)]

/-- `H¹`-style regularity contract in the current finite-dimensional setting. -/
def IsH1 (μ : Measure (W ι)) (u : W ι → ℝ) : Prop :=
  ∃ grad_u : W ι → W ι,
    HasWeakGradient u grad_u ∧
      IsL2Scalar μ u ∧
      IsL2Vector μ grad_u

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

/-- **`H¹` witness extraction**: unfolds the existential `IsH1` contract into a
reusable weak-gradient witness and `L²` certificates for downstream theorems. -/
theorem exists_weak_gradient_data_of_is_h1
    (μ : Measure (W ι)) (u : W ι → ℝ)
    (h_h1 : IsH1 μ u) :
    ∃ grad_u : W ι → W ι,
      HasWeakGradient u grad_u ∧ IsL2Scalar μ u ∧ IsL2Vector μ grad_u := by
  simpa only [IsH1] using h_h1

end LeanSharp
