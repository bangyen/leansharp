/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.ConvergenceHypotheses
import LeanSharp.Stochastic.Integrability

/-!
# Robbins-Monro Convergence Interface

This module exists to package Robbins-Monro style step-size assumptions together
with reusable ZSharp descent bounds, and to provide an interface theorem that
exposes almost-sure convergence statements for the stochastic objective process.

## Theorems

* `zsharp_robbins_monro_objective_limit_of_submartingale`.
* `zsharp_objective_as_convergence_of_bridge`.
* `zsharp_robbins_monro_almost_sure_convergence`.
* `zsharp_robbins_monro_objective_limit`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
omit [Fintype ι] in
/-- **End-to-end objective limit without opaque bridge assumptions** -/
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
  let _ := hη
  exact zsharp_objective_as_convergence_of_one_step_submartingale
    f w ℱ R h_adapted h_int h_step hbdd

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
  let _ := hη
  have h_env : ∀ T : ℕ,
      (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
        𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
        (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq) := by
    intro T
    exact zsharp_robbins_monro_descent_envelope L_smooth f w η z σsq T g_adv ℱ
      h_step h_desc_step h_int h_int_grad h_meas
  exact h_bridge hη h_env

/-- **Almost-sure convergence interface for ZSharp** -/
theorem zsharp_robbins_monro_almost_sure_convergence
    (L_smooth : NNReal) (f : W ι → ℝ)
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
  let _ := hη
  refine ⟨?_, ?_⟩
  · intro T
    exact zsharp_robbins_monro_descent_envelope L_smooth f w η z σsq T g_adv ℱ
      h_step h_desc_step h_int h_int_grad h_meas
  · rcases zsharp_neg_objective_uniform_l1_witness f w R hbdd_neg with ⟨R', hR'⟩
    have h_sub_neg : Submartingale (fun t ω => -f (w t ω)) ℱfil ℙ :=
      zsharp_neg_objective_submartingale_of_one_step f w ℱfil
        h_adapted_neg (fun t => (h_int t).neg) h_step_neg
    exact zsharp_objective_as_convergence_of_neg_submartingale f w ℱfil R' h_sub_neg hR'

/-- **End-to-end Robbins-Monro objective convergence** -/
theorem zsharp_robbins_monro_objective_limit
    (L_smooth : NNReal) (f : W ι → ℝ)
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
    zsharp_objective_as_convergence f w :=
  (zsharp_robbins_monro_almost_sure_convergence
    L_smooth f w η z σsq g_adv ℱ hη ℱfil
    h_adapted_neg h_step_neg R hbdd_neg
    h_step h_desc_step h_int h_int_grad h_meas).2

/-- **End-to-end objective-limit theorem from concrete model-level ZSharp hypotheses** -/
theorem zsharp_robbins_monro_objective_limit_of_model_descent_hypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model :
      zsharp_model_descent_hypotheses L_smooth f w η z σsq ℱ ℱfil) :
    zsharp_objective_as_convergence f w := by
  rcases h_model with ⟨h_rm, ⟨h_struct⟩, h_bridge, h_meas, h_desc_step⟩
  let g_adv (t : ℕ) (ω : Ω) := gradient f (w t ω)
  have ⟨h_int, h_int_grad⟩ := zsharp_structural_integrability f w η z σsq h_struct
  obtain ⟨R_neg, h_adapted_neg, h_step_neg, hbdd_neg⟩ :=
    zsharp_neg_process_data_of_objective_bridge_hypotheses f w ℱfil h_bridge
  exact @zsharp_robbins_monro_objective_limit ι _ Ω _ _
    L_smooth f w η z σsq g_adv ℱ h_rm ℱfil
    h_adapted_neg h_step_neg R_neg hbdd_neg
    (fun t => h_struct.h_step t) h_desc_step h_int h_int_grad h_meas

end LeanSharp
