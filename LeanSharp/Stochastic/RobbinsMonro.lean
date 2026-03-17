/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

/-!
# Robbins-Monro Convergence Interface

This module exists to package Robbins-Monro style step-size assumptions together
with reusable ZSharp descent bounds, and to provide an interface theorem that
exposes almost-sure convergence statements for the stochastic objective process.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

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

/-- **Robbins-Monro descent envelope for ZSharp**: under the standard conditional
descent assumptions, the cumulative weighted gradient energy up to horizon `T`
is bounded by initial-final objective gap plus variance accumulation. This is
the expectation-level seed used before almost-sure arguments. -/
theorem zsharp_robbins_monro_descent_envelope
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ) (T : ℕ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (h_step : ∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
      𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
      (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq) :=
  stochastic_zsharp_sequence_descent L_smooth f w η z σsq T g_adv ℱ
    h_step h_desc_step h_int h_int_grad h_meas

/-- **Almost-sure convergence interface for ZSharp**: this theorem packages the
Robbins-Monro assumptions with the sequence-descent envelope and an almost-sure
convergence seed (typically supplied by a supermartingale theorem) into one
specialized result for the Z-score filtered objective process. -/
theorem zsharp_robbins_monro_almost_sure_convergence
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (hη : robbins_monro_stepsize η)
    (h_step : ∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_as_seed : ∀ᵐ ω ∂ℙ, ∃ ℓ : ℝ,
      Filter.Tendsto (fun t => f (w t ω)) Filter.atTop (nhds ℓ)) :
    (∀ T : ℕ,
      (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
        𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
        (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq))
      ∧ (∀ᵐ ω ∂ℙ, ∃ ℓ : ℝ,
        Filter.Tendsto (fun t => f (w t ω)) Filter.atTop (nhds ℓ)) := by
  have hη_nonneg : ∀ t, 0 ≤ η t := robbins_monro_stepsize_nonneg η hη
  clear hη_nonneg
  refine ⟨?_, h_as_seed⟩
  intro T
  exact zsharp_robbins_monro_descent_envelope L_smooth f w η z σsq T g_adv ℱ
    h_step h_desc_step h_int h_int_grad h_meas

end LeanSharp
