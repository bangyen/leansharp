/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Mechanics.DescentSteps.ZScore
import LeanSharp.Stochastic.Mechanics.SharpnessMap
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Notation

/-!
# Integrability Derivations for ZSharp

This module provides the mathematical derivations to satisfy the `Integrable`
hypotheses required by Robbins-Monro convergence theorems. Instead of assuming
integrability at each step in the theorem signatures, we bundle those properties
into a structural assumption set.

## Definitions

* `ZSharpIntegrabilityAssumptions`.
* `ZSharpStructuralAssumptions`.

## Theorems

* `zsharp_integrability_of_assumptions`.
* `zsharp_structural_integrability`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Minimal integrability assumptions for ZSharp processes**: this bundle
contains only measurability and domination hypotheses needed to derive
integrability of objective values and squared gradient norms. It exists to
avoid requiring unrelated convergence assumptions when proving integrability
alone. -/
structure ZSharpIntegrabilityAssumptions (f : W ι → ℝ) (w : ℕ → Ω → W ι) where
  /-- Objective process is strongly measurable, enabling domination-based
  integrability. -/
  h_f_aemeas : ∀ t, AEStronglyMeasurable (fun ω => f (w t ω))
  /-- Squared gradient-norm process is strongly measurable, enabling
  domination-based integrability. -/
  h_g_aemeas : ∀ t, AEStronglyMeasurable (fun ω => ‖gradient f (w t ω)‖ ^ 2)
  /-- Dominating process for the objective value. -/
  f_dom : ℕ → Ω → ℝ
  /-- Dominating process for the squared gradient norm. -/
  g_dom : ℕ → Ω → ℝ
  /-- Integrability of the objective dominating process. -/
  h_f_dom_int : ∀ t, Integrable (f_dom t)
  /-- Integrability of the gradient-norm-squared dominating process. -/
  h_g_dom_int : ∀ t, Integrable (g_dom t)
  /-- Almost-everywhere domination for the objective value. -/
  h_f_dom_bound : ∀ t, ∀ᵐ ω ∂ℙ, ‖f (w t ω)‖ ≤ ‖f_dom t ω‖
  /-- Almost-everywhere domination for the squared gradient norm. -/
  h_g_dom_bound : ∀ t, ∀ᵐ ω ∂ℙ,
    ‖‖gradient f (w t ω)‖ ^ 2‖ ≤ ‖g_dom t ω‖

/-- **Structural ZSharp Assumptions**: A bundle of properties that imply the
integrability of the stochastic process. This captures all the regulatory conditions
needed for Robbins-Monro convergence without requiring manual proof in the middle
of descent lemmas. -/
structure ZSharpStructuralAssumptions
    (f : W ι → ℝ) (w : ℕ → Ω → W ι) (η : ℕ → ℝ)
    (z σsq : ℝ) where
  /-- Lipschitz constant of the gradient. -/
  L_smooth : NNReal
  /-- Gradient smoothness hypothesis witness. -/
  h_smooth : IsSmooth f L_smooth
  /-- Global lower bound hypothesis witness. -/
  h_bdd_below : BddBelow (Set.range f)
  /-- Gradient estimator variance hypothesis witness. -/
  h_var :
    ∀ t, HasBoundedVariance f (fun ω => gradient f (w t ω)) (w t ω) σsq
  /-- Objective process is strongly measurable, enabling domination-based
  integrability. -/
  h_f_aemeas : ∀ t, AEStronglyMeasurable (fun ω => f (w t ω))
  /-- Squared gradient-norm process is strongly measurable, enabling
  domination-based integrability. -/
  h_g_aemeas : ∀ t, AEStronglyMeasurable (fun ω => ‖gradient f (w t ω)‖ ^ 2)
  /-- Dominating process for the objective value. -/
  f_dom : ℕ → Ω → ℝ
  /-- Dominating process for the squared gradient norm. -/
  g_dom : ℕ → Ω → ℝ
  /-- Integrability of the objective dominating process. -/
  h_f_dom_int : ∀ t, Integrable (f_dom t)
  /-- Integrability of the gradient-norm-squared dominating process. -/
  h_g_dom_int : ∀ t, Integrable (g_dom t)
  /-- Almost-everywhere domination for the objective value. -/
  h_f_dom_bound : ∀ t, ∀ᵐ ω ∂ℙ, ‖f (w t ω)‖ ≤ ‖f_dom t ω‖
  /-- Almost-everywhere domination for the squared gradient norm. -/
  h_g_dom_bound : ∀ t, ∀ᵐ ω ∂ℙ, ‖‖gradient f (w t ω)‖ ^ 2‖ ≤ ‖g_dom t ω‖
  /-- Initial weight integrability witness. -/
  h_w0 : Integrable (fun ω => ‖w 0 ω‖ ^ 2)
  /-- Measurability of the stochastic process. -/
  h_meas : ∀ t, AEStronglyMeasurable (w t)
  /-- Step update rule witness. -/
  h_step :
    ∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω =
        stochasticZSharpStep (w t ω) η t z
          (fun ω' => gradient f (w t ω')) ω

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- **Integrability from minimal assumptions**: derives objective and
gradient-square integrability from the smallest reusable ZSharp assumption
bundle. This theorem exists as the core integrability API independent of
stronger structural convergence hypotheses. -/
theorem zsharp_integrability_of_assumptions (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (h_int : ZSharpIntegrabilityAssumptions f w) :
    (∀ t, Integrable (fun ω => f (w t ω))) ∧
    (∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2)) := by
  refine ⟨?_, ?_⟩
  · intro t
    exact (h_int.h_f_dom_int t).mono (h_int.h_f_aemeas t) (h_int.h_f_dom_bound t)
  · intro t
    exact (h_int.h_g_dom_int t).mono (h_int.h_g_aemeas t) (h_int.h_g_dom_bound t)

namespace ZSharpStructuralAssumptions

/-- **Projection to minimal integrability assumptions**: extracts the
integrability-relevant fields from the full structural bundle so downstream
results can depend on explicit minimal contracts. -/
def toIntegrabilityAssumptions
    {f : W ι → ℝ} {w : ℕ → Ω → W ι} {η : ℕ → ℝ} {z σsq : ℝ}
    (h_struct : ZSharpStructuralAssumptions f w η z σsq) :
    ZSharpIntegrabilityAssumptions f w where
  h_f_aemeas := h_struct.h_f_aemeas
  h_g_aemeas := h_struct.h_g_aemeas
  f_dom := h_struct.f_dom
  g_dom := h_struct.g_dom
  h_f_dom_int := h_struct.h_f_dom_int
  h_g_dom_int := h_struct.h_g_dom_int
  h_f_dom_bound := h_struct.h_f_dom_bound
  h_g_dom_bound := h_struct.h_g_dom_bound

end ZSharpStructuralAssumptions

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- **Structural Integrability**: The main theorem that derives the entire sequence of
integrability witnesses from structural assumptions. This theorem is intentionally
retained as a compatibility wrapper for callers that already package assumptions in
`ZSharpStructuralAssumptions`; minimal new results should prefer
`zsharp_integrability_of_assumptions`. -/
theorem zsharp_structural_integrability (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (η : ℕ → ℝ)
    (z σsq : ℝ)
    (h_struct : ZSharpStructuralAssumptions f w η z σsq) :
    (∀ t, Integrable (fun ω => f (w t ω))) ∧
    (∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2)) := by
  exact zsharp_integrability_of_assumptions f w h_struct.toIntegrabilityAssumptions

end LeanSharp
