/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Stochastic.Convergence.Process.Sequence
import LeanSharp.Stochastic.Rate

/-!
# O(1/T) Rate Tests

This module instantiates the headline `stochastic_zsharp_rate_O1_T` result on the
quadratic-bowl landscape, demonstrating that the $O(1/T)$ rate claim fires on a
concrete example with the canonical $\eta_t = 1 / (\mu (t+1))$ schedule.

## Examples

* `quadratic_bowl_O1_T_rate`.

## Theorems

* `zsharp_descent_envelope_zero_sequence`: the ZSharp conditional-descent
  envelope is non-vacuous for the degenerate zero sequence.
* `sam_descent_envelope_zero_sequence`: the same for the SAM envelope, the
  core premise of the SAM non-convex rate.
-/

namespace LeanSharp.Tests

open LeanSharp.QuadraticBowl
open ProbabilityTheory MeasureTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

local notation "W2" => W (Fin 2)

/-- The $O(1/T)$ rate specializes to the quadratic bowl with optimal point $w^* = 0$:
the expected squared distance to the optimum decays as $(‖w_0‖^2 + 1) / T$ under the
canonical strongly-convex schedule. -/
example (η : ℕ → ℝ) (z μ : ℝ) (g_adv : ℕ → Ω → W2) (ℱ : ℕ → MeasurableSpace Ω)
    (h_le : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_cond_bound : ∀ t, ∀ᵐ ω ∂volume,
      volume[fun ω' =>
        ‖weightSequence wInit η z g_adv (t + 1) ω' - 0‖ ^ 2 | ℱ t] ω ≤
      (1 - η t * μ) * ‖weightSequence wInit η z g_adv t ω - 0‖ ^ 2)
    (hμ : 0 < μ)
    (h_step : ∀ t, η t = 1 / (μ * (t + 1)))
    (h_align0 : StochasticAlignmentCondition (Ω := Ω) wInit 0 (g_adv 0) (η 0) μ z)
    (h_int : ∀ t, Integrable (fun ω => ‖weightSequence wInit η z g_adv t ω - 0‖ ^ 2)) :
    ∀ T : ℕ, T > 0 →
      𝔼[fun ω => ‖weightSequence wInit η z g_adv T ω - 0‖ ^ 2]
        ≤ (‖wInit - 0‖ ^ 2 + 1) / T := by
  exact stochastic_zsharp_rate_O1_T 0 wInit η z μ g_adv ℱ h_le h_cond_bound hμ h_step h_align0 h_int

/-- The $O(1/T)$ rate also holds when the alignment hypothesis is derived from a
deterministic geometric condition via the alignment bridge. -/
example (L : W2 → ℝ) (η : ℕ → ℝ) (z μ L_smooth : ℝ)
    (g_adv : ℕ → Ω → W2) (ℱ : ℕ → MeasurableSpace Ω) (ε : W2)
    (h_le : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_cond_bound : ∀ t, ∀ᵐ ω ∂volume,
      volume[fun ω' =>
        ‖weightSequence wInit η z g_adv (t + 1) ω' - 0‖ ^ 2 | ℱ t] ω ≤
      (1 - η t * μ) * ‖weightSequence wInit η z g_adv t ω - 0‖ ^ 2)
    (hμ : 0 < μ)
    (h_step : ∀ t, η t = 1 / (μ * (t + 1)))
    (h_g0 : g_adv 0 = fun _ => gradient L (wInit + ε))
    (h_align_det : AlignmentCondition wInit 0
      (filteredGradient (gradient L (wInit + ε)) z) μ L_smooth)
    (h_tight : η 0 * L_smooth ^ 2 ≤ μ)
    (h_eta : 0 ≤ η 0)
    (h_int : ∀ t, Integrable (fun ω => ‖weightSequence wInit η z g_adv t ω - 0‖ ^ 2)) :
    ∀ T : ℕ, T > 0 →
      𝔼[fun ω => ‖weightSequence wInit η z g_adv T ω - 0‖ ^ 2]
        ≤ (‖wInit - 0‖ ^ 2 + 1) / T := by
  exact stochastic_zsharp_rate_O1_T_of_deterministic_alignment L 0 wInit η z μ L_smooth
    g_adv ℱ ε h_le h_cond_bound hμ h_step h_g0 h_align_det h_tight h_eta h_int

/-- The `ZSharpDescentEnvelope` hypothesis is non-vacuous: it holds for the degenerate
zero sequence, where the filtered step stays at the minimum. -/
lemma zsharp_descent_envelope_zero_sequence
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ℱ : ℕ → MeasurableSpace Ω) (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (L_smooth σsq z : ℝ) (hL : 0 ≤ L_smooth) (hσ : 0 ≤ σsq) :
    ZSharpDescentEnvelope L_smooth toyLoss (fun (_ : ℕ) (_ : Ω) => (0 : W (Fin 2)))
      (fun _ => (1 : ℝ)) z σsq (fun (_ : ℕ) (_ : Ω) => (0 : W (Fin 2))) ℱ 0 := by
  unfold ZSharpDescentEnvelope
  have h_had_zero (a : W (Fin 2)) : hadamard (0 : W (Fin 2)) a = 0 := by
    apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
    ext i
    simp only [hadamard, WithLp.equiv_apply, WithLp.equiv_symm_apply, WithLp.ofLp_zero,
      Pi.zero_apply, zero_mul]
  have h_filt : filteredGradient (0 : W (Fin 2)) z = 0 := by
    unfold filteredGradient
    exact h_had_zero (zScoreMask (0 : W (Fin 2)) z)
  have h_step (ω' : Ω) :
      toyLoss (stochasticZSharpStep (0 : W (Fin 2)) (fun _ => (1 : ℝ)) 0 z
        (fun _ => (0 : W (Fin 2))) ω') = 0 := by
    have h_step0 : stochasticZSharpStep (0 : W (Fin 2)) (fun _ => (1 : ℝ)) 0 z
        (fun _ => (0 : W (Fin 2))) ω' = 0 := by
      simp only [stochasticZSharpStep, h_filt, one_smul, sub_self]
    rw [h_step0]
    norm_num [toyLoss, WithLp.equiv_apply]
  have h_ce_const : volume[fun _ : Ω => (0 : ℝ) | ℱ 0] =ᵐ[ℙ] (fun _ => (0 : ℝ)) := by
    exact Filter.Eventually.of_forall (fun ω => congrFun (condExp_const (h_meas 0) (0 : ℝ)) ω)
  have h_ce_step :
      volume[fun ω' => toyLoss (stochasticZSharpStep (0 : W (Fin 2)) (fun _ => (1 : ℝ)) 0 z
        (fun _ => (0 : W (Fin 2))) ω') | ℱ 0] =ᵐ[ℙ] (fun _ => (0 : ℝ)) := by
    have h_congr := condExp_congr_ae (μ := volume) (m₀ := ‹MeasureSpace Ω›.toMeasurableSpace)
      (m := ℱ 0) (f := fun ω' =>
        toyLoss (stochasticZSharpStep (0 : W (Fin 2)) (fun _ => (1 : ℝ)) 0 z
          (fun _ => (0 : W (Fin 2))) ω')) (g := fun _ : Ω => (0 : ℝ))
      (Filter.Eventually.of_forall h_step)
    exact h_congr.trans h_ce_const
  have h_grad0 : gradient toyLoss 0 = 0 := by
    rw [gradient_toy_eq]
    ext i
    norm_num [exactGradientToy, WithLp.equiv_apply, WithLp.equiv_symm_apply]
  have h_rhs : toyLoss (0 : W (Fin 2)) - (1 / 4) * ‖gradient toyLoss 0‖ ^ 2 +
      (1 ^ 2 * L_smooth / 2) * σsq = (L_smooth / 2) * σsq := by
    rw [h_grad0]
    norm_num [toyLoss, WithLp.equiv_apply]
  filter_upwards [h_ce_step] with ω h1
  calc
    volume[fun ω' => toyLoss (stochasticZSharpStep (0 : W (Fin 2)) (fun _ => (1 : ℝ)) 0 z
        (fun _ => (0 : W (Fin 2))) ω') | ℱ 0] ω
      = (0 : ℝ) := h1
    _ ≤ toyLoss (0 : W (Fin 2)) - (1 / 4) * ‖gradient toyLoss 0‖ ^ 2 +
        (1 ^ 2 * L_smooth / 2) * σsq := by
      rw [h_rhs]
      exact mul_nonneg (div_nonneg hL (by norm_num : (0 : ℝ) ≤ 2)) hσ

/-- The `SAMDescentEnvelope` hypothesis — the core assumption of the SAM non-convex
rate — is non-vacuous: it holds for the degenerate zero sequence. The SAM envelope is
the ZSharp envelope at the effective variance `σsq + 2 L² ρ²`, which stays nonnegative,
so the degenerate witness transfers directly. -/
lemma sam_descent_envelope_zero_sequence
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (ℱ : ℕ → MeasurableSpace Ω) (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (L_smooth σsq ρ z : ℝ) (hL : 0 ≤ L_smooth) (hσ : 0 ≤ σsq) :
    SAMDescentEnvelope L_smooth toyLoss (fun (_ : ℕ) (_ : Ω) => (0 : W (Fin 2)))
      (fun _ => (1 : ℝ)) z σsq ρ (fun (_ : ℕ) (_ : Ω) => (0 : W (Fin 2))) ℱ 0 := by
  unfold SAMDescentEnvelope
  refine zsharp_descent_envelope_zero_sequence ℱ h_meas L_smooth
    (σsq + 2 * L_smooth ^ 2 * ρ ^ 2) z hL ?_
  positivity

end LeanSharp.Tests
