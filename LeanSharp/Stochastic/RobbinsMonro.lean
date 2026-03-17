/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.ConvergenceBridge

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
Robbins-Monro assumptions with the sequence-descent envelope and a concrete
Mathlib-backed transformed-process convergence premise into one specialized
result for the Z-score filtered objective process. -/
theorem zsharp_robbins_monro_almost_sure_convergence
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (hη : robbins_monro_stepsize η)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_adapted_neg : StronglyAdapted ℱfil (fun t ω => -f (w t ω)))
    (h_step_neg :
      ∀ t, (fun ω => -f (w t ω)) ≤ᵐ[ℙ] ℙ[fun ω => -f (w (t + 1) ω) | ℱfil t])
    (R : NNReal)
    (hbdd_neg : ∀ t, eLpNorm (fun ω => -f (w t ω)) 1 ℙ ≤ R)
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
  · rcases zsharp_neg_objective_uniform_l1_witness f w R hbdd_neg with ⟨R', hR'⟩
    have h_int_neg : ∀ t, Integrable (fun ω => -f (w t ω)) ℙ := by
      intro t
      exact (h_int t).neg
    have h_sub_neg : Submartingale (fun t ω => -f (w t ω)) ℱfil ℙ :=
      zsharp_neg_objective_submartingale_of_one_step f w ℱfil
        h_adapted_neg h_int_neg h_step_neg
    exact zsharp_objective_as_convergence_of_neg_submartingale f w ℱfil R' h_sub_neg hR'

/-- **End-to-end Robbins-Monro objective convergence**: convenience projection of
`zsharp_robbins_monro_almost_sure_convergence` that returns only the almost-sure
objective limit statement after all envelope assumptions are supplied. -/
theorem zsharp_robbins_monro_objective_limit
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (hη : robbins_monro_stepsize η)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_adapted_neg : StronglyAdapted ℱfil (fun t ω => -f (w t ω)))
    (h_step_neg :
      ∀ t, (fun ω => -f (w t ω)) ≤ᵐ[ℙ] ℙ[fun ω => -f (w (t + 1) ω) | ℱfil t])
    (R : NNReal)
    (hbdd_neg : ∀ t, eLpNorm (fun ω => -f (w t ω)) 1 ℙ ≤ R)
    (h_step : ∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    zsharp_objective_as_convergence f w := by
  exact (zsharp_robbins_monro_almost_sure_convergence
    L_smooth f w η z σsq g_adv ℱ hη ℱfil
    h_adapted_neg h_step_neg R hbdd_neg
    h_step h_desc_step h_int h_int_grad h_meas).2

/-- Objective-space convenience wrapper: this theorem accepts the one-step
supermartingale inequality directly in objective coordinates and internally
derives the transformed `-f` one-step monotonicity needed by the convergence
bridge. -/
theorem zsharp_robbins_monro_objective_limit_of_objective_step
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (hη : robbins_monro_stepsize η)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_adapted_neg : StronglyAdapted ℱfil (fun t ω => -f (w t ω)))
    (h_step_obj :
      ∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
    (R : NNReal)
    (hbdd_neg : ∀ t, eLpNorm (fun ω => -f (w t ω)) 1 ℙ ≤ R)
    (h_step : ∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    zsharp_objective_as_convergence f w := by
  have h_step_neg :
      ∀ t, (fun ω => -f (w t ω)) ≤ᵐ[ℙ] ℙ[fun ω => -f (w (t + 1) ω) | ℱfil t] :=
    zsharp_neg_step_mono_of_objective_supermartingale_step f w ℱfil h_step_obj
  exact zsharp_robbins_monro_objective_limit
    L_smooth f w η z σsq g_adv ℱ hη ℱfil h_adapted_neg h_step_neg R hbdd_neg
    h_step h_desc_step h_int h_int_grad h_meas

/-- Fully objective-coordinate convenience wrapper: callers provide both the
one-step supermartingale condition and uniform `L¹` bound for `t ↦ f (w t ·)`.
The transformed-process (`-f`) assumptions are derived internally. -/
theorem zsharp_robbins_monro_objective_limit_of_objective_step_and_l1
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (hη : robbins_monro_stepsize η)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_adapted_neg : StronglyAdapted ℱfil (fun t ω => -f (w t ω)))
    (h_step_obj :
      ∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
    (R : NNReal)
    (hbdd_obj : ∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R)
    (h_step : ∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    zsharp_objective_as_convergence f w := by
  have hbdd_neg : ∀ t, eLpNorm (fun ω => -f (w t ω)) 1 ℙ ≤ R :=
    zsharp_neg_uniform_l1_of_objective_uniform_l1 f w R hbdd_obj
  exact zsharp_robbins_monro_objective_limit_of_objective_step
    L_smooth f w η z σsq g_adv ℱ hη ℱfil h_adapted_neg h_step_obj R hbdd_neg
    h_step h_desc_step h_int h_int_grad h_meas

end LeanSharp
