/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence
import Mathlib.Order.Filter.Basic
import Mathlib.Probability.Martingale.Convergence
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
/-- **End-to-end objective limit without opaque bridge assumptions**: this theorem
uses explicit one-step submartingale hypotheses and L¹ bounds to derive almost-sure
convergence of the ZSharp objective process via Mathlib's martingale convergence
theorem. -/
theorem zsharp_robbins_monro_objective_limit_of_submartingale
    (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (hη : robbins_monro_stepsize η)
    (R : NNReal)
    (h_adapted : StronglyAdapted ℱ (fun t ω => f (w t ω)))
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_step :
      ∀ t, (fun ω => f (w t ω)) ≤ᵐ[ℙ] ℙ[fun ω => f (w (t + 1) ω) | ℱ t])
    (hbdd : ∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R) :
    zsharp_objective_as_convergence f w := by
  have hη_nonneg : ∀ t, 0 ≤ η t := robbins_monro_stepsize_nonneg η hη
  clear hη_nonneg
  exact zsharp_objective_as_convergence_of_one_step_submartingale
    f w ℱ R h_adapted h_int h_step hbdd

/-- **Bridge application theorem**: given a proved bridge contract and the
descent envelope hypotheses, obtain almost-sure convergence of the objective
sequence for ZSharp. -/
theorem zsharp_objective_as_convergence_of_bridge
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (hη : robbins_monro_stepsize η)
    (h_bridge : zsharp_supermartingale_as_bridge L_smooth f w η σsq)
    (h_step : ∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    zsharp_objective_as_convergence f w := by
  have h_env : ∀ T : ℕ,
      (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
        𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
        (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq) := by
    intro T
    exact zsharp_robbins_monro_descent_envelope L_smooth f w η z σsq T g_adv ℱ
      h_step h_desc_step h_int h_int_grad h_meas
  exact h_bridge hη h_env

/-- **Almost-sure convergence interface for ZSharp**: this theorem packages the
Robbins-Monro assumptions with the sequence-descent envelope and an almost-sure
convergence bridge (typically supplied by a supermartingale theorem) into one
specialized result for the Z-score filtered objective process. -/
theorem zsharp_robbins_monro_almost_sure_convergence
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (hη : robbins_monro_stepsize η)
    (h_bridge : zsharp_supermartingale_as_bridge L_smooth f w η σsq)
    (h_step : ∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    (∀ T : ℕ,
      (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
        𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
        (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq))
      ∧ zsharp_objective_as_convergence f w := by
  have hη_nonneg : ∀ t, 0 ≤ η t := robbins_monro_stepsize_nonneg η hη
  clear hη_nonneg
  refine ⟨?_, ?_⟩
  · intro T
    exact zsharp_robbins_monro_descent_envelope L_smooth f w η z σsq T g_adv ℱ
      h_step h_desc_step h_int h_int_grad h_meas
  · exact zsharp_objective_as_convergence_of_bridge L_smooth f w η z σsq g_adv ℱ
      hη h_bridge h_step h_desc_step h_int h_int_grad h_meas

/-- **End-to-end Robbins-Monro objective convergence**: convenience projection of
`zsharp_robbins_monro_almost_sure_convergence` that returns only the almost-sure
objective limit statement after all envelope assumptions are supplied. -/
theorem zsharp_robbins_monro_objective_limit
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (hη : robbins_monro_stepsize η)
    (h_bridge : zsharp_supermartingale_as_bridge L_smooth f w η σsq)
    (h_step : ∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    zsharp_objective_as_convergence f w := by
  exact (zsharp_robbins_monro_almost_sure_convergence
    L_smooth f w η z σsq g_adv ℱ hη h_bridge h_step h_desc_step h_int h_int_grad h_meas).2

end LeanSharp
