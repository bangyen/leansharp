/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.ConvergenceBridge
import LeanSharp.Stochastic.Integrability

/-!
# Convergence Hypothesis Bundles

This module provides packaged hypothesis bundles for ZSharp objective
convergence. These bundles group Robbins-Monro step-size assumptions,
objective-bridge data, and sequence-descent envelope premises to
simplify interface theorems.

## Definitions

* `zsharp_objective_bridge_hypotheses`.
* `zsharp_strongest_descent_hypotheses`.
* `zsharp_model_descent_hypotheses`.

## Theorems

* `zsharp_robbins_monro_descent_envelope`.
* `zsharp_model_descent_hypotheses_of_structural`.
* `zsharp_strongest_descent_hypotheses_of_model_descent_hypotheses`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Robbins-Monro descent envelope for ZSharp** -/
theorem zsharp_robbins_monro_descent_envelope
    (L_smooth : NNReal) (f : W ι → ℝ)
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

/-- Bridge-ready objective assumptions in a single bundle -/
def zsharp_objective_bridge_hypotheses
    (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) : Prop :=
  ∃ R : NNReal,
    StronglyAdapted ℱfil (fun t ω => f (w t ω))
      ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
      ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R)

/-- Strongest currently exposed ZSharp descent hypothesis bundle for objective
limits. -/
def zsharp_strongest_descent_hypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) : Prop :=
  robbins_monro_stepsize η
    ∧ zsharp_objective_bridge_hypotheses f w ℱfil
    ∧ (∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    ∧ (∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    ∧ (∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    ∧ (∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    ∧ (∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)

/-- Concrete model-level hypothesis bundle for ZSharp objective convergence -/
def zsharp_model_descent_hypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) : Prop :=
  robbins_monro_stepsize η
    ∧ Nonempty (ZSharpStructuralAssumptions f w η z σsq)
    ∧ zsharp_objective_bridge_hypotheses f w ℱfil
    ∧ (∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    ∧ (∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z
        (fun ω'' => gradient f (w t ω'')) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- **Structural-to-Model Hypothesis Promotion** -/
theorem zsharp_model_descent_hypotheses_of_structural
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_struct : ZSharpStructuralAssumptions f w η z σsq)
    (h_rm : robbins_monro_stepsize η)
    (h_bridge : zsharp_objective_bridge_hypotheses f w ℱfil)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z
        (fun ω'' => gradient f (w t ω'')) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq) :
    zsharp_model_descent_hypotheses L_smooth f w η z σsq ℱ ℱfil :=
  ⟨h_rm, ⟨h_struct⟩, h_bridge, h_meas, h_desc_step⟩

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Repackages concrete model-level ZSharp hypotheses into the strongest descent
bundle used by downstream interface theorems. -/
theorem zsharp_strongest_descent_hypotheses_of_model_descent_hypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model :
      zsharp_model_descent_hypotheses L_smooth f w η z σsq ℱ ℱfil) :
    zsharp_strongest_descent_hypotheses L_smooth f w η z σsq
      (fun t ω => gradient f (w t ω)) ℱ ℱfil := by
  rcases h_model with ⟨h_rm, ⟨h_struct⟩, h_bridge, h_meas, h_desc_step⟩
  have h_int_all := zsharp_structural_integrability f w η z σsq h_struct
  exact ⟨h_rm, h_bridge, h_struct.h_step, h_desc_step, h_int_all.1, h_int_all.2, h_meas⟩

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Builds the objective-bridge contract from concrete model-level ZSharp hypotheses -/
theorem zsharp_objective_bridge_hypotheses_of_model_descent_hypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model :
      zsharp_model_descent_hypotheses L_smooth f w η z σsq ℱ ℱfil) :
    zsharp_objective_bridge_hypotheses f w ℱfil :=
  h_model.2.2.1

omit [Fintype ι] [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Extracts transformed-process bridge data from `zsharp_objective_bridge_hypotheses` -/
theorem zsharp_neg_process_data_of_objective_bridge_hypotheses
    (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_bridge_obj : zsharp_objective_bridge_hypotheses f w ℱfil) :
    ∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => -f (w t ω))
        ∧ (∀ t, (fun ω => -f (w t ω)) ≤ᵐ[ℙ] ℙ[fun ω => -f (w (t + 1) ω) | ℱfil t])
        ∧ (∀ t, eLpNorm (fun ω => -f (w t ω)) 1 ℙ ≤ R) := by
  rcases h_bridge_obj with ⟨R, h_adapted_obj, h_step_obj, hbdd_obj⟩
  rcases zsharp_neg_bridge_data_of_objective_data
      f w ℱfil R h_adapted_obj h_step_obj hbdd_obj with
    ⟨h_adapted_neg, h_step_neg, hbdd_neg⟩
  exact ⟨R, h_adapted_neg, h_step_neg, hbdd_neg⟩

end LeanSharp
