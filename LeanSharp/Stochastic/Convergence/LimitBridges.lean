/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.ProcessLimits
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

* `robbins_monro_stepsize_nonneg`.
* `robbins_monro_stepsize_square_summable`.
* `robbins_monro_stepsize_tendsto_zero`.
* `zsharp_neg_objective_submartingale_of_one_step`.
* `zsharp_neg_objective_uniform_l1_witness`.
* `zsharp_neg_uniform_l1_of_objective_uniform_l1`.
* `zsharp_neg_step_mono_of_objective_supermartingale_step`.
* `zsharp_neg_adapted_of_objective_adapted`.
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

/-- Exposes the nonnegativity component of `robbins_monro_stepsize` so downstream
proofs can reuse it without repeatedly unpacking the full conjunction. -/
theorem robbins_monro_stepsize_nonneg (η : ℕ → ℝ)
    (hη : robbins_monro_stepsize η) : ∀ t, 0 ≤ η t :=
  hη.1

/-- Exposes square-summability from `robbins_monro_stepsize`, which is the key
summability side-condition in Robbins-Monro convergence arguments. -/
theorem robbins_monro_stepsize_square_summable (η : ℕ → ℝ)
    (hη : robbins_monro_stepsize η) : Summable (fun t => (η t) ^ 2) :=
  hη.2.1

/-- Exposes vanishing step sizes from `robbins_monro_stepsize`. This captures
the asymptotic stabilization condition used in stochastic approximation. -/
theorem robbins_monro_stepsize_tendsto_zero (η : ℕ → ℝ)
    (hη : robbins_monro_stepsize η) : Filter.Tendsto η Filter.atTop (nhds 0) :=
  hη.2.2

omit [Fintype ι] in
/-- Constructor theorem that turns one-step transformed-objective assumptions into
a `Submartingale` certificate for `t ↦ -f (w t ·)`. -/
theorem zsharp_neg_objective_submartingale_of_one_step
    (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_adapted_neg : StronglyAdapted ℱ (fun t ω => -f (w t ω)))
    (h_int_neg : ∀ t, Integrable (fun ω => -f (w t ω)) ℙ)
    (h_step_neg :
      ∀ t, (fun ω => -f (w t ω)) ≤ᵐ[ℙ] ℙ[fun ω => -f (w (t + 1) ω) | ℱ t]) :
    Submartingale (fun t ω => -f (w t ω)) ℱ ℙ := by
  exact submartingale_nat h_adapted_neg h_int_neg h_step_neg

/- The transformed objective needs a uniform `L¹` witness before applying
Mathlib's a.e. submartingale convergence theorem. -/
omit [Fintype ι] [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Packages an explicit uniform `L¹` witness for the transformed objective
process. This keeps the final convergence theorem free of existential
bookkeeping in downstream proofs. -/
theorem zsharp_neg_objective_uniform_l1_witness
    (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (R : NNReal)
    (hbdd_neg : ∀ t, eLpNorm (fun ω => -f (w t ω)) 1 ℙ ≤ R) :
    ∃ R' : NNReal, ∀ t, eLpNorm (fun ω => -f (w t ω)) 1 ℙ ≤ R' :=
  ⟨R, hbdd_neg⟩

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

omit [Fintype ι] in
/-- **Martingale-to-a.s. objective convergence**: if the objective process is a
martingale and uniformly `L¹` bounded, almost-sure objective convergence follows
by reducing to the submartingale convergence interface theorem. -/
theorem zsharp_objective_as_convergence_of_martingale
    (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (R : NNReal)
    (h_mart : Martingale (fun t ω => f (w t ω)) ℱ ℙ)
    (hbdd : ∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R) :
    zsharp_objective_as_convergence f w := by
  exact zsharp_objective_as_convergence_of_submartingale
    f w ℱ R h_mart.submartingale hbdd

omit [Fintype ι] in
/-- **One-step bridge constructor**: packages explicit adaptedness, integrability,
and one-step conditional expectation monotonicity into a submartingale certificate,
then applies the theorem-backed Mathlib bridge to get almost-sure objective
convergence. -/
theorem zsharp_objective_as_convergence_of_one_step_submartingale
    (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (R : NNReal)
    (h_adapted : StronglyAdapted ℱ (fun t ω => f (w t ω)))
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_step :
      ∀ t, (fun ω => f (w t ω)) ≤ᵐ[ℙ] ℙ[fun ω => f (w (t + 1) ω) | ℱ t])
    (hbdd : ∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R) :
    zsharp_objective_as_convergence f w := by
  have h_sub : Submartingale (fun t ω => f (w t ω)) ℱ ℙ :=
    submartingale_nat h_adapted h_int h_step
  exact zsharp_objective_as_convergence_of_submartingale f w ℱ R h_sub hbdd

omit [Fintype ι] in
/-- **Sign-flip convergence transfer**: if the transformed objective process
`t ↦ -f (w t ·)` converges almost surely, then the original objective process
`t ↦ f (w t ·)` also converges almost surely by continuity of negation. -/
theorem zsharp_objective_as_convergence_of_neg_submartingale
    (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (R : NNReal)
    (h_sub_neg : Submartingale (fun t ω => -f (w t ω)) ℱ ℙ)
    (hbdd_neg : ∀ t, eLpNorm (fun ω => -f (w t ω)) 1 ℙ ≤ R) :
    zsharp_objective_as_convergence f w := by
  have h_ae_tendsto_neg :
      ∀ᵐ ω ∂ℙ, Filter.Tendsto (fun t => -f (w t ω)) Filter.atTop
        (nhds (ℱ.limitProcess (fun t ω => -f (w t ω)) ℙ ω)) :=
    h_sub_neg.ae_tendsto_limitProcess hbdd_neg
  filter_upwards [h_ae_tendsto_neg] with ω hω
  refine ⟨-(ℱ.limitProcess (fun t ω => -f (w t ω)) ℙ ω), ?_⟩
  have h_neg_cont :
      Filter.Tendsto (fun x : ℝ => -x)
        (nhds (ℱ.limitProcess (fun t ω => -f (w t ω)) ℙ ω))
        (nhds (-(ℱ.limitProcess (fun t ω => -f (w t ω)) ℙ ω))) :=
    continuous_neg.tendsto (ℱ.limitProcess (fun t ω => -f (w t ω)) ℙ ω)
  have h_tendsto_obj :
      Filter.Tendsto (fun t => -(-f (w t ω))) Filter.atTop
        (nhds (-(ℱ.limitProcess (fun t ω => -f (w t ω)) ℙ ω))) :=
    h_neg_cont.comp hω
  simp only [neg_neg] at h_tendsto_obj
  exact h_tendsto_obj

end LeanSharp
