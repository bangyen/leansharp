/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Process.Descent
import Mathlib.Tactic.Linarith

/-!
# Stochastic ZSharp Process - Sequence Bounds

This module aggregates individual descent steps into sequence-level bounds
governing the entire optimization trajectory.

## Main Definitions
* `ZSharpDescentEnvelope`: Shared conditional-descent premise for a single step.
* `SAMDescentEnvelope`: SAM-specific conditional-descent premise with perturbation penalty.

## Main Theorems
* `stochastic_zsharp_sequence_descent`: Accumulation of descent steps over time.
* `sam_sequence_descent`: Accumulation of SAM descent envelopes over time.
* `zsharp_envelope_of_pointwise_descent`: The bridge from a pointwise one-step
  descent to the conditional envelope.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory NNReal

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **ZSharp Descent Envelope**: the conditional expected progress of the objective
after a single stochastic ZSharp step at time `t`. This is the shared one-step
descent premise used by all sequence-level convergence theorems: the expected
objective at the next iterate is bounded by the current objective minus a
gradient-norm term plus a variance term. -/
def ZSharpDescentEnvelope (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω) (t : ℕ) : Prop :=
  ∀ᵐ ω ∂ℙ,
    volume[fun ω' => f (stochasticZSharpStep (w t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 + (η t ^ 2 * L_smooth / 2) * σsq

/-- **SAM Descent Envelope**: Conditional descent with the SAM perturbation
error absorbed into the effective variance term. The quarter-gradient form
matches the sequence-level interface used by the existing stochastic theorem. -/
def SAMDescentEnvelope (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq ρ : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω) (t : ℕ) : Prop :=
  ZSharpDescentEnvelope L_smooth f w η z (σsq + 2 * L_smooth ^ 2 * ρ ^ 2) g_adv ℱ t

/-- **Envelope from Pointwise Descent**: If the one-step objective decrease holds
pointwise almost everywhere and the current objective and gradient norm are adapted
to the filtration `ℱ t`, then the conditional `ZSharpDescentEnvelope` follows. This
is the filtration/measurability bridge needed to derive the envelope for the filtered
sequence from the concrete stochastic descent step. Instantiating `σsq` with the
effective variance `σsq + 2L²ρ²` yields the `SAMDescentEnvelope` by definition. -/
theorem zsharp_envelope_of_pointwise_descent (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω) (t : ℕ)
    (h_step_t : ∀ᵐ ω ∂ℙ, w (t + 1) ω = stochasticZSharpStep (w t ω) η t z (g_adv t) ω)
    (h_pointwise : ∀ᵐ ω ∂ℙ,
      f (w (t + 1) ω) ≤ f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 +
        (η t ^ 2 * L_smooth / 2) * σsq)
    (h_meas_f : AEStronglyMeasurable (m := ℱ t) (fun ω => f (w t ω)) volume)
    (h_meas_grad : AEStronglyMeasurable (m := ℱ t)
      (fun ω => ‖gradient f (w t ω)‖ ^ 2) volume)
    (h_meas_ft : ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_int_t : Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_int_next : Integrable (fun ω => f (w (t + 1) ω)) ℙ) :
    ZSharpDescentEnvelope L_smooth f w η z σsq g_adv ℱ t := by
  let A (ω : Ω) : ℝ := f (w (t + 1) ω)
  let B (ω : Ω) : ℝ := f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 +
    (η t ^ 2 * L_smooth / 2) * σsq
  have h_pt : A ≤ᵐ[ℙ] B := by
    simpa only [A, B] using h_pointwise
  have h_meas_B : AEStronglyMeasurable (m := ℱ t) B volume := by
    dsimp only [B]
    have h1 : AEStronglyMeasurable (m := ℱ t)
        (fun ω => (η t / 4) * ‖gradient f (w t ω)‖ ^ 2) volume :=
      h_meas_grad.const_mul (η t / 4)
    have h2 : AEStronglyMeasurable (m := ℱ t)
        (fun ω => f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2) volume :=
      h_meas_f.sub h1
    have h3 : AEStronglyMeasurable (m := ℱ t)
        (fun ω => (η t ^ 2 * L_smooth / 2) * σsq) volume := by
      exact stronglyMeasurable_const.aestronglyMeasurable
    exact h2.add h3
  have h_int_B : Integrable B ℙ := by
    dsimp only [B]
    exact (h_int_t.sub (h_int_grad.const_mul _)).add (integrable_const _)
  have h_ce_mono : volume[A | ℱ t] ≤ᵐ[ℙ] volume[B | ℱ t] :=
    condExp_mono h_int_next h_int_B h_pt
  have h_ce_B : volume[B | ℱ t] =ᵐ[ℙ] B :=
    condExp_of_aestronglyMeasurable' h_meas_ft h_meas_B h_int_B
  have h_ce_congr :
      volume[fun ω' => f (stochasticZSharpStep (w t ω') η t z (g_adv t) ω') | ℱ t] =ᵐ[ℙ]
      volume[A | ℱ t] := by
    apply condExp_congr_ae
    filter_upwards [h_step_t] with ω' hω'
    rw [← hω']
  unfold ZSharpDescentEnvelope
  filter_upwards [h_ce_congr, h_ce_mono, h_ce_B] with ω hc hm hb
  calc
    volume[fun ω' => f (stochasticZSharpStep (w t ω') η t z (g_adv t) ω') | ℱ t] ω
      = volume[A | ℱ t] ω := hc
    _ ≤ volume[B | ℱ t] ω := hm
    _ = f (w t ω) - (η t / 4) * ‖gradient f (w t ω)‖ ^ 2 +
        (η t ^ 2 * L_smooth / 2) * σsq := hb

/-- **ZSharp Sequence Descent**:
Aggregates the individual descent steps into a sequence-level bound.
This is the fundamental lemma used to prove the $O(1/\sqrt{T})$ convergence rate. -/
theorem stochastic_zsharp_sequence_descent (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq : ℝ) (T : ℕ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (h_step : ∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω = stochasticZSharpStep (w t ω) η t z (g_adv t) ω)
    (h_desc_step : ∀ t, ZSharpDescentEnvelope L_smooth f w η z σsq g_adv ℱ t)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
      𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
      (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq) := by
  induction T with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, sub_self, add_zero]
      exact le_refl _
  | succ t ih =>
      have h_sum1 :
          (∑ k ∈ Finset.range (t + 1),
            (η k / 4) * ∫ ω, ‖gradient f (w k ω)‖ ^ 2 ∂ℙ) =
          (∑ k ∈ Finset.range t, (η k / 4) * ∫ ω, ‖gradient f (w k ω)‖ ^ 2 ∂ℙ) +
          (η t / 4) * ∫ ω, ‖gradient f (w t ω)‖ ^ 2 ∂ℙ := Finset.sum_range_succ _ _
      have h_sum2 : (∑ k ∈ Finset.range (t + 1), (η k ^ 2 * L_smooth / 2) * σsq) =
          (∑ k ∈ Finset.range t, (η k ^ 2 * L_smooth / 2) * σsq) +
          (η t ^ 2 * L_smooth / 2) * σsq := Finset.sum_range_succ _ _
      have h_exp_step : ∫ ω, f (w (t + 1) ω) ∂ℙ ≤
          ∫ ω, f (w t ω) ∂ℙ - (η t / 4) * ∫ ω, ‖gradient f (w t ω)‖ ^ 2 ∂ℙ +
          (η t ^ 2 * L_smooth / 2) * σsq :=
        stochastic_expected_descent_step L_smooth f w η z σsq t g_adv ℱ
          (h_step t) (h_desc_step t) (h_int t) (h_int_grad t) (h_meas t)
      linarith

/-- **SAM Sequence Descent**: Accumulates SAM descent envelopes using the
effective variance `σ² + 2L²ρ²`. -/
theorem sam_sequence_descent (L_smooth : ℝ) (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ) (z σsq ρ : ℝ) (T : ℕ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (h_step : ∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω = stochasticZSharpStep (w t ω) η t z (g_adv t) ω)
    (h_desc_step : ∀ t, SAMDescentEnvelope L_smooth f w η z σsq ρ g_adv ℱ t)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ)
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient f (w t ω)‖ ^ 2) ℙ)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    (∑ t ∈ Finset.range T, (η t / 4) *
        𝔼[fun ω => ‖gradient f (w t ω)‖ ^ 2]) ≤
      𝔼[fun ω => f (w 0 ω)] - 𝔼[fun ω => f (w T ω)] +
      (∑ t ∈ Finset.range T,
        (η t ^ 2 * L_smooth / 2) * (σsq + 2 * L_smooth ^ 2 * ρ ^ 2)) := by
  exact stochastic_zsharp_sequence_descent L_smooth f w η z
    (σsq + 2 * L_smooth ^ 2 * ρ ^ 2) T g_adv ℱ h_step
    (fun t => h_desc_step t) h_int h_int_grad h_meas

end LeanSharp
