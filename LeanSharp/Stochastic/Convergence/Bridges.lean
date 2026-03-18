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

* `zsharp_objective_as_convergence`.
* `robbins_monro_stepsize`.
* `zsharp_supermartingale_as_bridge`.

## Theorems

* `zsharp_objective_as_convergence_of_submartingale`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- Predicate capturing almost-sure objective convergence for a stochastic
iterate process. This exists so bridge assumptions can target a single reusable
contract rather than repeating the same event signature across theorems. -/
def zsharp_objective_as_convergence (f : W ι → ℝ) (w : ℕ → Ω → W ι) : Prop :=
  ∀ᵐ ω ∂ℙ, ∃ ℓ : ℝ,
    Filter.Tendsto (fun t => f (w t ω)) Filter.atTop (nhds ℓ)

/-- Robbins-Monro step-size assumptions for stochastic approximation:
nonnegativity, square-summability, and vanishing step sizes. -/
def robbins_monro_stepsize (η : ℕ → ℝ) : Prop :=
  (∀ t, 0 ≤ η t) ∧ Summable (fun t => (η t) ^ 2) ∧
    Filter.Tendsto η Filter.atTop (nhds 0)

/-- **Supermartingale-to-a.s. bridge contract for ZSharp objectives**: this
predicate packages the expected-descent envelope and Robbins-Monro step-size
assumptions into a single hypothesis that returns almost-sure convergence of the
objective sequence. It isolates the exact theorem gap needed to connect
expectation-level control to pathwise convergence. -/
def zsharp_supermartingale_as_bridge
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (σsq : ℝ) : Prop :=
  robbins_monro_stepsize η →
  (∀ T : ℕ,
    (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
      𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
      (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq)) →
  zsharp_objective_as_convergence f w

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
    zsharp_objective_as_convergence f w := by
  have h_ae_tendsto :
      ∀ᵐ ω ∂ℙ, Filter.Tendsto (fun t => f (w t ω)) Filter.atTop
        (nhds (ℱ.limitProcess (fun t ω => f (w t ω)) ℙ ω)) :=
    h_sub.ae_tendsto_limitProcess hbdd
  filter_upwards [h_ae_tendsto] with ω hω
  exact ⟨ℱ.limitProcess (fun t ω => f (w t ω)) ℙ ω, hω⟩

end LeanSharp
