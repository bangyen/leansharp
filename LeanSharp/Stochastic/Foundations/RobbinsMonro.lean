/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Assumptions
import LeanSharp.Stochastic.Foundations.Integrability
import LeanSharp.Stochastic.Foundations.Martingale

/-!
# Robbins-Monro Convergence Interface

This module exists to package Robbins-Monro style step-size assumptions together
with reusable ZSharp descent bounds, and to provide an interface theorem that
exposes almost-sure convergence statements for the stochastic objective process.

## Theorems

* `zsharp_robbins_monro_objective_limit_with_martingale_model`.
* `zsharp_objective_as_convergence_of_bridge`.
* `zsharp_robbins_monro_almost_sure_convergence`.
* `zsharp_robbins_monro_almost_sure_convergence_of_model_descent_hypotheses`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

omit [Fintype ι] in
/-- **Objective limit from submartingale hypotheses**: derives almost-sure
objective convergence from adaptation, integrability, and one-step
submartingale inequality assumptions. The explicit update recursion is exposed
in `robbins_monro_update_martingale_model.h_update`. -/
theorem zsharp_robbins_monro_objective_limit_with_martingale_model
    (f : W ι → ℝ)
    (w : ℕ → Ω → W ι)
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

/-- **Bridge application theorem** -/
theorem zsharp_objective_as_convergence_of_bridge
    (L_smooth : NNReal) (f : W ι → ℝ)
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
    exact stochastic_zsharp_sequence_descent L_smooth f w η z σsq T g_adv ℱ
      h_step h_desc_step h_int h_int_grad h_meas
  exact h_bridge hη h_env

/-- **Almost-sure convergence interface for ZSharp** -/
theorem zsharp_robbins_monro_almost_sure_convergence
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
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
  refine ⟨?_, ?_⟩
  · intro T
    exact stochastic_zsharp_sequence_descent L_smooth f w η z σsq T g_adv ℱ
      h_step h_desc_step h_int h_int_grad h_meas
  · have h_sub_neg : Submartingale (fun t ω => -f (w t ω)) ℱfil ℙ := by
      apply submartingale_nat
      · exact h_adapted_neg
      · intro t; exact (h_int t).neg
      · exact h_step_neg
    have h_ae_tendsto_neg :
        ∀ᵐ ω ∂ℙ, Filter.Tendsto (fun t => -f (w t ω)) Filter.atTop
          (nhds (ℱfil.limitProcess (fun t ω => -f (w t ω)) ℙ ω)) :=
      h_sub_neg.ae_tendsto_limitProcess hbdd_neg
    filter_upwards [h_ae_tendsto_neg] with ω hω
    refine ⟨-(ℱfil.limitProcess (fun t ω => -f (w t ω)) ℙ ω), ?_⟩
    have h_neg_cont :
        Filter.Tendsto (fun x : ℝ => -x)
          (nhds (ℱfil.limitProcess (fun t ω => -f (w t ω)) ℙ ω))
          (nhds (-(ℱfil.limitProcess (fun t ω => -f (w t ω)) ℙ ω))) :=
      continuous_neg.tendsto (ℱfil.limitProcess (fun t ω => -f (w t ω)) ℙ ω)
    have h_tendsto_obj :
        Filter.Tendsto (fun t => -(-f (w t ω))) Filter.atTop
          (nhds (-(ℱfil.limitProcess (fun t ω => -f (w t ω)) ℙ ω))) :=
      h_neg_cont.comp hω
    simpa only [neg_neg] using h_tendsto_obj

/-- **End-to-end almost-sure convergence theorem from concrete model-level ZSharp
hypotheses**: returns both the descent-envelope inequality family and the
almost-sure objective convergence statement. -/
theorem zsharp_robbins_monro_almost_sure_convergence_of_model_descent_hypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model :
      zsharp_model_descent_hypotheses L_smooth f w η z σsq ℱ ℱfil) :
    (∀ T : ℕ,
      (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
        𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
        (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq))
      ∧ zsharp_objective_as_convergence f w := by
  rcases h_model with ⟨_, ⟨h_struct⟩, ⟨R_obj, h_adapted_obj, h_step_obj, hbdd_obj⟩,
    h_meas, h_desc_step⟩
  let g_adv (t : ℕ) (ω : Ω) := gradient f (w t ω)
  have ⟨h_int, h_int_grad⟩ := zsharp_structural_integrability f w η z σsq h_struct
  let R_neg := R_obj
  have h_adapted_neg : StronglyAdapted ℱfil (fun t ω => -f (w t ω)) := h_adapted_obj.neg
  have h_step_neg (t : ℕ) : (fun ω => -f (w t ω)) ≤ᵐ[ℙ]
      ℙ[fun ω => -f (w (t + 1) ω) | ℱfil t] := by
    have h_neg_obj : (fun ω => -f (w t ω)) ≤ᵐ[ℙ]
        (fun ω => -ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ω) := by
      filter_upwards [h_step_obj t] with ω hω
      linarith
    have hcond_neg := (condExp_neg (μ := ℙ) (m := ℱfil t) (f := fun ω => f (w (t + 1) ω))).symm
    exact h_neg_obj.trans_eq hcond_neg
  have hbdd_neg (t : ℕ) : eLpNorm (fun ω => -f (w t ω)) 1 ℙ ≤ R_neg := by
    have hfun : (fun ω => -f (w t ω)) = -(fun ω => f (w t ω)) := rfl
    rw [hfun, eLpNorm_neg]
    exact hbdd_obj t
  exact @zsharp_robbins_monro_almost_sure_convergence ι _ Ω _ _
    L_smooth f w η z σsq g_adv ℱ ℱfil
    h_adapted_neg h_step_neg R_neg hbdd_neg
    (fun t => h_struct.h_step t) h_desc_step h_int h_int_grad h_meas

end LeanSharp
