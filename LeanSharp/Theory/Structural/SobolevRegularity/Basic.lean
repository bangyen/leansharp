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
# Sobolev Regularity - Basic Definitions

This module introduces $L^2$ regularity predicates and weak-derivative interface
contracts for scalar, vector, and Hessian fields.

## Main Definitions
* `IsL2Scalar`: $L^2$ regularity for scalar fields.
* `HasWeakGradient`: Interface contract for weak gradients.
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

end LeanSharp
