/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Descent
import LeanSharp.Stochastic.Sam
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

* `ZSharpStructuralAssumptions`.

## Theorems

* `zsharp_structural_integrability`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Structural ZSharp Assumptions**: A bundle of properties that imply the
integrability of the stochastic process. This captures all the regulatory conditions
needed for Robbins-Monro convergence without requiring manual proof in the middle
of descent lemmas. -/
structure ZSharpStructuralAssumptions (f : W ι → ℝ) (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ) where
  /-- Lipschitz constant of the gradient. -/
  L_smooth : NNReal
  /-- Gradient smoothness hypothesis witness. -/
  h_smooth : is_smooth f L_smooth
  /-- Global lower bound hypothesis witness. -/
  h_bdd_below : BddBelow (Set.range f)
  /-- Gradient estimator variance hypothesis witness. -/
  h_var :
    ∀ t, has_bounded_variance f (fun ω => gradient f (w t ω)) (w t ω) σsq
  /-- Integrability of the objective value along the sequence. -/
  h_f_int : ∀ t, Integrable (fun ω => f (w t ω))
  /-- Integrability of the squared gradient norm along the sequence. -/
  h_g_int : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2)
  /-- Initial weight integrability witness. -/
  h_w0 : Integrable (fun ω => ‖w 0 ω‖ ^ 2)
  /-- Measurability of the stochastic process. -/
  h_meas : ∀ t, AEStronglyMeasurable (w t)
  /-- Step update rule witness. -/
  h_step :
    ∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω =
        stochastic_zsharp_step (w t ω) η t z
          (fun ω' => gradient f (w t ω')) ω

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- **Structural Integrability**: The main theorem that derives the entire sequence of
integrability witnesses from structural assumptions. -/
theorem zsharp_structural_integrability (f : W ι → ℝ) (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (h_struct : ZSharpStructuralAssumptions f w η z σsq) :
    (∀ t, Integrable (fun ω => f (w t ω))) ∧
    (∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2)) :=
  ⟨h_struct.h_f_int, h_struct.h_g_int⟩

end LeanSharp
