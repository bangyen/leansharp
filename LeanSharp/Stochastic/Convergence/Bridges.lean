/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Process
import Mathlib.Order.Filter.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Topology.Basic

/-!
# Robbins-Monro Convergence Bridge

This module provides the bridge between expectation-level descent bounds and
almost-sure convergence statements. It uses Mathlib's martingale convergence
theorems to establish objective-process limits under submartingale-style
assumptions.

## Definitions

* `ZSharpObjectiveAsConvergence`.
* `RobbinsMonroStepsize`.
* `ZSharpSupermartingaleAsBridge`.

## Theorems

* `zsharp_objective_as_convergence_of_submartingale`.
* `zsharp_objective_as_convergence_of_bridge_contract`.
* `zsharp_objective_as_convergence_of_submartingale_bridge_contract`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- Predicate capturing almost-sure objective convergence for a stochastic
iterate process. This exists so bridge assumptions can target a single reusable
contract rather than repeating the same event signature across theorems. -/
def ZSharpObjectiveAsConvergence (f : W ι → ℝ) (w : ℕ → Ω → W ι) : Prop :=
  ∀ᵐ ω ∂ℙ, ∃ ℓ : ℝ,
    Filter.Tendsto (fun t => f (w t ω)) Filter.atTop (nhds ℓ)

/-- Robbins-Monro step-size assumptions for stochastic approximation:
nonnegativity, square-summability, and vanishing step sizes. -/
def RobbinsMonroStepsize (η : ℕ → ℝ) : Prop :=
  (∀ t, 0 ≤ η t) ∧ Summable (fun t => (η t) ^ 2) ∧
    Filter.Tendsto η Filter.atTop (nhds 0)

/-- **Supermartingale-to-a.s. bridge contract for ZSharp objectives**: this
predicate packages the expected-descent envelope and Robbins-Monro step-size
assumptions into a single hypothesis that returns almost-sure convergence of the
objective sequence. It isolates the exact theorem gap needed to connect
expectation-level control to pathwise convergence. -/
def ZSharpSupermartingaleAsBridge
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (σsq : ℝ) : Prop :=
  RobbinsMonroStepsize η →
  (∀ T : ℕ,
    (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
      𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
      (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq)) →
  ZSharpObjectiveAsConvergence f w

omit [Fintype ι] in
/-- **Concrete Mathlib bridge for objective convergence**: if the objective process
`t ↦ f (w t ·)` is a submartingale and is uniformly L¹-bounded, then almost-sure
objective convergence follows directly from Mathlib's a.e. martingale convergence
theorem. This theorem exists to replace opaque bridge assumptions with explicit,
theorem-backed hypotheses. -/
theorem zsharp_objective_as_convergence_of_submartingale
    (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (R : NNReal)
    (h_sub : Submartingale (fun t ω => f (w t ω)) ℱ ℙ)
    (hbdd : ∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R) :
    ZSharpObjectiveAsConvergence f w := by
  have h_ae_tendsto :
      ∀ᵐ ω ∂ℙ, Filter.Tendsto (fun t => f (w t ω)) Filter.atTop
        (nhds (ℱ.limitProcess (fun t ω => f (w t ω)) ℙ ω)) :=
    h_sub.ae_tendsto_limitProcess hbdd
  filter_upwards [h_ae_tendsto] with ω hω
  exact ⟨ℱ.limitProcess (fun t ω => f (w t ω)) ℙ ω, hω⟩

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- **Bridge-contract eliminator**: this theorem turns the project-level
`ZSharpSupermartingaleAsBridge` package and Robbins-Monro step-size assumptions
into an explicit almost-sure objective convergence conclusion. It exists as the
canonical entry point for callers that treat bridge hypotheses as a reusable API
layer over Mathlib convergence machinery. -/
theorem zsharp_objective_as_convergence_of_bridge_contract
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (σsq : ℝ)
    (hη : RobbinsMonroStepsize η)
    (h_env : ∀ T : ℕ,
      (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
        𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
        (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq))
    (h_bridge : ZSharpSupermartingaleAsBridge L_smooth f w η σsq) :
    ZSharpObjectiveAsConvergence f w :=
  h_bridge hη h_env

omit [Fintype ι] in
/-- **Submartingale-to-bridge instantiation theorem**: given submartingale and
uniform `L¹` bounds for the objective process, this theorem builds the project
bridge contract and immediately derives almost-sure objective convergence. This
is an explicit project-level formalization wrapper around Mathlib's martingale
convergence theorem. -/
theorem zsharp_objective_as_convergence_of_submartingale_bridge_contract
    (f : W ι → ℝ)
    (w : ℕ → Ω → W ι)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (R : NNReal)
    (h_sub : Submartingale (fun t ω => f (w t ω)) ℱ ℙ)
    (hbdd : ∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R) :
    ZSharpObjectiveAsConvergence f w := by
  exact zsharp_objective_as_convergence_of_submartingale f w ℱ R h_sub hbdd

end LeanSharp
