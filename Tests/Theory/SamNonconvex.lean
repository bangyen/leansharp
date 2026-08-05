/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Stochastic.Convergence.Process.Sequence
import LeanSharp.Stochastic.Foundations.SAMOracle
import LeanSharp.Stochastic.Foundations.Schedules.SamNonconvex
import LeanSharp.Stochastic.Foundations.Schedules.StronglyConvex

/-!
# SAM Non-Convex Rate Tests

These examples exercise the public SAM perturbation, oracle, and finite-horizon
rate interfaces on the quadratic-bowl landscape.

## Main Theorems
This module contains API-level examples rather than new mathematical results.
-/

namespace LeanSharp.Tests

open LeanSharp.QuadraticBowl
open ProbabilityTheory MeasureTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

local notation "W2" => W (Fin 2)

/-- The quadratic-bowl perturbation obeys the declared SAM radius bound. -/
example (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ‖samPerturbation toyLoss wInit ρ‖ ≤ ρ := by
  exact norm_samPerturbation_le toyLoss wInit ρ hρ

/-- The conditional oracle exposes its martingale-centering contract directly. -/
example (f : W2 → ℝ) (w : ℕ → Ω → W2) (z ρ σsq : ℝ)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (oracle : SAMConditionalOracle f w z ρ σsq ℱfil) :
    ∀ t, ℙ[oracle.noise t | ℱfil t] =ᵐ[ℙ] (fun _ => 0) := by
  exact oracle.noise_cond_mean

/-- The complete conditional rate theorem specializes to the quadratic bowl. -/
example (z L_smooth σsq ρ : ℝ) (η : ℕ → ℝ)
    (g_adv : ℕ → Ω → W2) (T : ℕ) (hT : T > 0)
    (ℱ : ℕ → MeasurableSpace Ω)
    (h_step : ∀ t, η t = 1 / (2 * L_smooth * Real.sqrt T))
    (h_L_pos : L_smooth > 0)
    (h_bdd : BddBelow (Set.range toyLoss))
    (h_int_L : ∀ t, Integrable
      (fun ω => toyLoss (weightSequence wInit η z g_adv t ω)))
    (h_int_grad : ∀ t, Integrable
      (fun ω => ‖gradient toyLoss
        (weightSequence wInit η z g_adv t ω)‖ ^ 2) ℙ)
    (h_desc : ∀ t, SAMDescentEnvelope L_smooth toyLoss
      (weightSequence wInit η z g_adv) η z σsq ρ g_adv ℱ t)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    (1 / (T : ℝ)) * (∑ t ∈ Finset.range T,
      𝔼[fun ω => ‖gradient toyLoss
        (weightSequence wInit η z g_adv t ω)‖ ^ 2])
      ≤ (8 * L_smooth * (toyLoss wInit - sInf (Set.range toyLoss)) +
        (σsq + 2 * L_smooth ^ 2 * ρ ^ 2)) / Real.sqrt (T : ℝ) := by
  exact sam_nonconvex_rate_complete toyLoss wInit z L_smooth σsq ρ η g_adv T hT ℱ
    h_step h_L_pos h_bdd h_int_L h_int_grad h_desc h_meas

/-- The pointwise-to-conditional envelope bridge yields the SAM descent envelope
for the filtered sequence: given a pointwise one-step SAM descent bound for the
`weightSequence` and adaptation of the iterate to the filtration, the conditional
`SAMDescentEnvelope` follows. -/
example {ι : Type*} [Fintype ι] {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (L : SmoothObjective ι) (w0 : W ι) (η : ℕ → ℝ) (z σsq ρ : ℝ)
    (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω) (t : ℕ)
    (h_pointwise : ∀ᵐ ω ∂ℙ,
      L.toFun (weightSequence w0 η z g_adv (t + 1) ω) ≤
        L.toFun (weightSequence w0 η z g_adv t ω) -
          (η t / 4) * ‖gradient L.toFun (weightSequence w0 η z g_adv t ω)‖ ^ 2 +
          (η t ^ 2 * (L.smoothness : ℝ) / 2) *
            (σsq + 2 * (L.smoothness : ℝ) ^ 2 * ρ ^ 2))
    (h_meas_f : AEStronglyMeasurable (m := ℱ t)
      (fun ω => L.toFun (weightSequence w0 η z g_adv t ω)) volume)
    (h_meas_grad : AEStronglyMeasurable (m := ℱ t)
      (fun ω => ‖gradient L.toFun (weightSequence w0 η z g_adv t ω)‖ ^ 2) volume)
    (h_meas_ft : ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_int_t : Integrable
      (fun ω => L.toFun (weightSequence w0 η z g_adv t ω)) ℙ)
    (h_int_grad : Integrable
      (fun ω => ‖gradient L.toFun (weightSequence w0 η z g_adv t ω)‖ ^ 2) ℙ)
    (h_int_next : Integrable
      (fun ω => L.toFun (weightSequence w0 η z g_adv (t + 1) ω)) ℙ) :
    SAMDescentEnvelope (L.smoothness : ℝ) L.toFun (weightSequence w0 η z g_adv)
      η z σsq ρ g_adv ℱ t := by
  exact zsharp_envelope_of_pointwise_descent (L.smoothness : ℝ) L.toFun
    (weightSequence w0 η z g_adv) η z (σsq + 2 * (L.smoothness : ℝ) ^ 2 * ρ ^ 2)
    g_adv ℱ t (weight_sequence_step_eventually w0 η z g_adv t) h_pointwise
    h_meas_f h_meas_grad h_meas_ft h_int_t h_int_grad h_int_next

end LeanSharp.Tests
