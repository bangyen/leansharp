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

/-- Bridge-ready objective assumptions in a single bundle, and transformed-process
(`-f`) assumptions are derived internally. This exists to expose one stable
interface for objective-coordinate convergence applications. -/
def zsharp_objective_bridge_hypotheses
    (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) : Prop :=
  ∃ R : NNReal,
    StronglyAdapted ℱfil (fun t ω => f (w t ω))
      ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
      ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R)

/-- Strongest currently exposed ZSharp descent hypothesis bundle for objective
limits. It packages Robbins-Monro step-size assumptions, objective-bridge data,
and the sequence-descent envelope premises into one reusable contract. -/
def zsharp_strongest_descent_hypotheses
    (L_smooth : ℝ) (f : W ι → ℝ)
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

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Concrete model-level hypothesis bundle for ZSharp objective convergence.
Unlike `zsharp_strongest_descent_hypotheses`, this spells out objective-bridge
assumptions directly (`R`, adaptedness, one-step objective monotonicity, `L¹`
control) before they are repackaged into bridge interfaces. -/
def zsharp_model_descent_hypotheses
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) : Prop :=
  robbins_monro_stepsize η
    ∧ (∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => f (w t ω))
        ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
        ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    ∧ (∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    ∧ (∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    ∧ (∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    ∧ (∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    ∧ (∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)

/-- Filtration-specialized model-level bundle that removes explicit
measurability-side-condition plumbing by fixing conditional expectations to
`ℱfil t`. -/
def zsharp_model_descent_hypotheses_filtration
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) : Prop :=
  robbins_monro_stepsize η
    ∧ (∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => f (w t ω))
        ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
        ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    ∧ (∀ t, ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochastic_zsharp_step (w t ω) η t z (g_adv t) ω)
    ∧ (∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z (g_adv t) ω') | ℱfil t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    ∧ (∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    ∧ (∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- **Structural-to-Model Hypothesis Promotion**:
This theorem provides the bridge from low-level structural assumptions (smoothness,
variance, boundedness) to the model-level hypotheses used by the convergence
interface. It discharges the `Integrable` requirements using the derivations
in `LeanSharp.Stochastic.Integrability`. -/
@[nolint unusedArguments]
theorem zsharp_model_descent_hypotheses_of_structural_spec
    (L_smooth : ℝ) (h_L_pos : 0 ≤ L_smooth) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_struct : ZSharpStructuralAssumptions f w η z σsq)
    (h_rm : robbins_monro_stepsize η)
    (h_bridge : ∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => f (w t ω))
        ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
        ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z
        (fun ω'' => gradient f (w t ω'')) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    zsharp_model_descent_hypotheses L_smooth f w η z σsq
      (fun t ω => gradient f (w t ω)) ℱ ℱfil := by
  exact ⟨
    h_rm,
    h_bridge,
    (by intro t; simpa only using (h_struct.h_step t)),
    h_desc_step,
    h_int,
    h_int_grad,
    h_meas
  ⟩

omit [IsProbabilityMeasure (volume : Measure Ω)] in
theorem zsharp_model_descent_hypotheses_of_structural
    (L_smooth : ℝ) (h_L_pos : 0 ≤ L_smooth) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_struct : ZSharpStructuralAssumptions f w η z σsq)
    (h_rm : robbins_monro_stepsize η)
    (h_bridge : ∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => f (w t ω))
        ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
        ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    (h_desc_step : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => f (stochastic_zsharp_step (w t ω') η t z
        (fun ω'' => gradient f (w t ω'')) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    zsharp_model_descent_hypotheses
      L_smooth f w η z σsq (fun t ω => gradient f (w t ω)) ℱ ℱfil := by
  exact zsharp_model_descent_hypotheses_of_structural_spec
    L_smooth h_L_pos f w η z σsq ℱ ℱfil h_struct h_rm h_bridge
    h_desc_step h_int h_int_grad h_meas

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Promotes the filtration-specialized model bundle into the generic
model-descent bundle by deriving the conditional-expectation measurability side
condition from the filtration itself. -/
theorem zsharp_model_descent_hypotheses_of_filtration
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model_fil :
      zsharp_model_descent_hypotheses_filtration L_smooth f w η z σsq g_adv ℱfil) :
    zsharp_model_descent_hypotheses
      L_smooth f w η z σsq g_adv (fun t => ℱfil t) ℱfil := by
  rcases h_model_fil with
    ⟨hη, h_bridge_obj, h_step, h_desc_step, h_int, h_int_grad⟩
  have h_meas : ∀ t, (fun s => ℱfil s) t ≤ ‹MeasureSpace Ω›.toMeasurableSpace := by
    intro t
    exact ℱfil.le t
  exact ⟨hη, h_bridge_obj, h_step, h_desc_step, h_int, h_int_grad, h_meas⟩

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Builds the objective-bridge contract from concrete model-level ZSharp
hypotheses. -/
theorem zsharp_objective_bridge_hypotheses_of_model_descent_hypotheses
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model :
      zsharp_model_descent_hypotheses L_smooth f w η z σsq g_adv ℱ ℱfil) :
    zsharp_objective_bridge_hypotheses f w ℱfil :=
  h_model.2.1

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Repackages concrete model-level ZSharp hypotheses into the strongest descent
bundle used by downstream interface theorems. -/
theorem zsharp_strongest_descent_hypotheses_of_model_descent_hypotheses
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model :
      zsharp_model_descent_hypotheses L_smooth f w η z σsq g_adv ℱ ℱfil) :
    zsharp_strongest_descent_hypotheses L_smooth f w η z σsq g_adv ℱ ℱfil := by
  rcases h_model with
    ⟨hη, h_bridge_obj, h_step, h_desc_step, h_int, h_int_grad, h_meas⟩
  exact ⟨hη, h_bridge_obj, h_step, h_desc_step, h_int, h_int_grad, h_meas⟩

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Projects objective-bridge assumptions directly from the strongest currently
available ZSharp descent hypothesis bundle. -/
theorem zsharp_objective_bridge_hypotheses_of_strongest_descent_hypotheses
    (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_strong :
      zsharp_strongest_descent_hypotheses L_smooth f w η z σsq g_adv ℱ ℱfil) :
    zsharp_objective_bridge_hypotheses f w ℱfil :=
  h_strong.2.1

omit [Fintype ι] [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Extracts transformed-process bridge data from
`zsharp_objective_bridge_hypotheses`. This theorem is the handoff from a single
objective-coordinate contract to the `-f` convergence bridge prerequisites. -/
theorem zsharp_neg_process_data_of_objective_bridge_hypotheses
    (f : W ι → ℝ) (w : ℕ → Ω → W ι)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_bridge_obj : zsharp_objective_bridge_hypotheses f w ℱfil) :
    ∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => -f (w t ω))
        ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
        ∧ (∀ t, eLpNorm (fun ω => -f (w t ω)) 1 ℙ ≤ R) := by
  rcases h_bridge_obj with ⟨R, h_adapted_obj, h_step_obj, hbdd_obj⟩
  rcases zsharp_neg_bridge_data_of_objective_data
      f w ℱfil R h_adapted_obj h_step_obj hbdd_obj with
    ⟨h_adapted_neg, h_step_neg, hbdd_neg⟩
  clear h_step_neg
  exact ⟨R, h_adapted_neg, h_step_obj, hbdd_neg⟩

end LeanSharp
