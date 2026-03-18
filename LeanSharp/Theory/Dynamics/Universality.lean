/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import LeanSharp.Theory.Structural.HessianContraction
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Z-Score Universality

This module starts the formalization of the **Z-score filtered distribution**.
The goal is to characterize the statistical properties of the filtered gradient
to establish optimality lower bounds and custom Central Limit Theorems (CLT).

## Main definitions

* `filteredDistribution`: The probability measure of the filtered gradient
  given a base noise distribution and a z-score threshold.
* `filteredCharFun`: Characteristic function of the filtered distribution.

## Main contracts

* `FilteredDistributionSymmetric`: Distribution-level symmetry interface used
  by downstream universality arguments.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory NNReal

variable {ι : Type*} [Fintype ι]
variable [MeasurableSpace (W ι)]

/-- **Filtered Gradient Distribution**:
Given a measurable space of parameters and a base probability measure `μ` on the
noise (e.g., Gaussian or Cauchy), the `filteredDistribution` is the pushforward
measure under the filtering transformation. -/
noncomputable def filteredDistribution
    (μ : Measure (W ι)) (z : ℝ) : Measure (W ι) :=
  μ.map (filteredGradient · z)

/-- **Filtered Characteristic Function**:
The characteristic function of the filtered distribution, crucial for proving
the custom CLT for Z-score SAM. -/
noncomputable def filteredCharFun
    (μ : Measure (W ι)) (z : ℝ) (t : W ι) : ℂ :=
  ∫ x, Complex.exp (Complex.I * inner ℝ t (filteredGradient x z)) ∂μ

section Universality

/-- Symmetry contract for filtered distributions.
This predicate exists to separate distribution-level invariance assumptions from
downstream universality arguments, so CLT-style theorems can depend on a stable
interface instead of a specific base-noise construction. -/
def FilteredDistributionSymmetric (μ : Measure (W ι)) (z : ℝ) : Prop :=
  ∀ (A : Set (W ι)), MeasurableSet A →
    filteredDistribution μ z A = filteredDistribution μ z (Neg.neg '' A)

end Universality

end LeanSharp
