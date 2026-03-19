/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Foundations.RobbinsMonro
import LeanSharp.Theory.Dynamics.Convergence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Notation

/-!
# Strongly Convex Schedules

This module exists to provide the strongly-convex schedule recursion and explicit
`O(1/T)` rate lemmas, while exposing iterate construction used by other schedule
analyses.

## Definitions

* `weightSequence`: recursive iterate process for stochastic ZSharp updates.

## Theorems

* `zsharp_strongly_convex_rate`: explicit `O(1/T)` rate under contraction assumptions.
* `weight_sequence_step_eventually`: recursion identity for `weightSequence`.
* `weight_sequence_robbins_monro_almost_sure_convergence_of_model_descent_hypotheses`:
  almost-sure convergence for the concrete `weightSequence` process.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- Recursively define the weight iterates for ZSharp. -/
noncomputable def weightSequence (w0 : W ι) (η : ℕ → ℝ) (z : ℝ)
    (g_adv : ℕ → Ω → W ι) : ℕ → Ω → W ι
| 0, _ => w0
| t+1, ω => stochasticZSharpStep (weightSequence w0 η z g_adv t ω) η t z (g_adv t) ω

/-- **Strongly Convex Induction Step**: The $T \to T+1$ recursion for the $O(1/T)$ rate. -/
private lemma strongly_convex_induction_step (t : ℕ) (μ C : ℝ) (η : ℕ → ℝ)
    (w_star w0 : W ι) (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (h_le : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_cond_bound : ∀ t, ∀ᵐ ω ∂volume,
      volume[fun ω' =>
        ‖weightSequence w0 η z g_adv (t + 1) ω' - w_star‖ ^ 2 | ℱ t] ω ≤
      (1 - η t * μ) * ‖weightSequence w0 η z g_adv t ω - w_star‖ ^ 2)
    (h_int : ∀ t, Integrable (fun ω => ‖weightSequence w0 η z g_adv t ω - w_star‖ ^ 2))
    (h_ih : 𝔼[fun ω => ‖weightSequence w0 η z g_adv t ω - w_star‖ ^ 2] ≤ C / t)
    (h_step : η t = 1 / (μ * (t + 1))) (hμ : μ > 0) (ht : 0 < t) :
    𝔼[fun ω => ‖weightSequence w0 η z g_adv (t + 1) ω - w_star‖ ^ 2] ≤
      C / (t + 1) := by
  have h_contraction_factor : 1 - (η t) * μ = (t : ℝ) / (t + 1) := by
    rw [h_step]; field_simp [hμ.ne']; ring
  have h_iter : 𝔼[fun ω => ‖weightSequence w0 η z g_adv (t + 1) ω - w_star‖ ^ 2] ≤
      ((t : ℝ) / (t + 1)) *
        𝔼[fun ω => ‖weightSequence w0 η z g_adv t ω - w_star‖ ^ 2] := by
    rw [(integral_condExp (h_le t)).symm]
    apply le_trans (integral_mono_ae integrable_condExp
      (Integrable.const_mul (h_int t) (1 - η t * μ)) (h_cond_bound t))
    rw [integral_const_mul, h_contraction_factor]
  calc 𝔼[fun ω => ‖weightSequence w0 η z g_adv (t + 1) ω - w_star‖ ^ 2]
    _ ≤ ((t : ℝ) / (t + 1)) *
        𝔼[fun ω => ‖weightSequence w0 η z g_adv t ω - w_star‖ ^ 2] := h_iter
    _ ≤ ((t : ℝ) / (t + 1)) * (C / t) := mul_le_mul_of_nonneg_left h_ih (by positivity)
    _ = C / (t + 1) := by field_simp [ht.ne']

/-- **$O(1/T)$ recursion rate under contraction assumptions**:
if each step satisfies the stated conditional contraction and the canonical
step-size schedule $\eta_t = 1 / (\mu (t+1))$ with `μ > 0`, then the expected
squared distance to `w_star` decays at rate `1/T`. -/
theorem zsharp_strongly_convex_rate (w_star : W ι) w0
    (η : ℕ → ℝ) (z μ : ℝ) (g_adv : ℕ → Ω → W ι)
    (ℱ : ℕ → MeasurableSpace Ω)
    (h_le : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_cond_bound : ∀ t, ∀ᵐ ω ∂volume,
      volume[fun ω' =>
        ‖weightSequence w0 η z g_adv (t + 1) ω' - w_star‖ ^ 2 | ℱ t] ω ≤
      (1 - η t * μ) * ‖weightSequence w0 η z g_adv t ω - w_star‖ ^ 2)
    (hμ : 0 < μ)
    (h_step : ∀ t, η t = 1 / (μ * (t + 1)))
    (h_align0 : StochasticAlignmentCondition w_star w0 η 0 z μ (g_adv 0))
    (h_int : ∀ t, Integrable (fun ω => ‖weightSequence w0 η z g_adv t ω - w_star‖ ^ 2)) :
    ∀ T : ℕ, T > 0 →
      𝔼[fun ω => ‖weightSequence w0 η z g_adv T ω - w_star‖ ^ 2]
        ≤ (‖w0 - w_star‖ ^ 2 + 1) / T := by
  intro T hT
  let C := ‖w0 - w_star‖ ^ 2 + 1
  induction T with
  | zero => contradiction
  | succ t ih =>
    by_cases ht : t = 0
    · rw [ht, Nat.cast_one, div_one]
      have h_bound :
          𝔼[fun ω => ‖stochasticZSharpStep w0 η 0 z (g_adv 0) ω - w_star‖ ^ 2] ≤
          (1 - (η 0) * μ) * ‖w0 - w_star‖ ^ 2 :=
        stochastic_zsharp_convergence w_star w0 η 0 z μ h_align0
      have h_zero : 1 - (η 0) * μ = 0 := by
        rw [h_step 0]; field_simp [hμ.ne']; ring
      rw [h_zero, zero_mul] at h_bound
      exact h_bound.trans (by linarith [pow_two_nonneg ‖w0 - w_star‖])
    · have hval : C / ↑(t + 1) = C / (↑t + 1) := by norm_cast
      rw [hval]
      exact strongly_convex_induction_step t μ C η w_star w0 g_adv ℱ h_le h_cond_bound h_int
        (ih (Nat.pos_of_ne_zero ht)) (h_step t) hμ (Nat.pos_of_ne_zero ht)

omit [IsProbabilityMeasure (volume : Measure Ω)] in
/-- Recursion identity for `weightSequence` as an almost-everywhere update rule.
This lemma exists so concrete-sequence convergence theorems can provide the exact
step contract expected by Robbins-Monro interfaces. -/
theorem weight_sequence_step_eventually
    (w0 : W ι) (η : ℕ → ℝ) (z : ℝ) (g_adv : ℕ → Ω → W ι) :
    ∀ t, ∀ᵐ ω ∂ℙ,
      weightSequence w0 η z g_adv (t + 1) ω =
        stochasticZSharpStep (weightSequence w0 η z g_adv t ω) η t z (g_adv t) ω := by
  intro t
  exact Filter.Eventually.of_forall (fun ω => by
    simp only [weightSequence])

/-- **Concrete Robbins-Monro a.s. convergence for `weightSequence`**:
specializes the model-level convergence interface to the recursively defined
Z-score iterate process. This theorem exists to expose an explicit sequence-level
almost-sure convergence result for the concrete SGD recursion. -/
theorem weight_sequence_robbins_monro_almost_sure_convergence_of_model_descent_hypotheses
    (L_smooth : NNReal) (f : W ι → ℝ)
    (w0 : W ι) (η : ℕ → ℝ) (z σsq : ℝ)
    (g_adv : ℕ → Ω → W ι)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_model :
      ZSharpModelDescentHypotheses L_smooth f (weightSequence w0 η z g_adv) η z σsq ℱ ℱfil) :
    (∀ t, ∀ᵐ ω ∂ℙ,
      weightSequence w0 η z g_adv (t + 1) ω =
        stochasticZSharpStep (weightSequence w0 η z g_adv t ω) η t z (g_adv t) ω)
      ∧
    (∀ T : ℕ,
      (∑ t ∈ Finset.range T,
        (η t / 4) * 𝔼[fun ω => ‖gradient f (weightSequence w0 η z g_adv t ω)‖ ^ 2]) ≤
        𝔼[fun ω => f (weightSequence w0 η z g_adv 0 ω)] -
          𝔼[fun ω => f (weightSequence w0 η z g_adv T ω)] +
        (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) * σsq))
      ∧ ZSharpObjectiveAsConvergence f (weightSequence w0 η z g_adv) := by
  have h_step := weight_sequence_step_eventually (w0 := w0) (η := η) (z := z) (g_adv := g_adv)
  have h_core :=
    zsharp_robbins_monro_almost_sure_convergence_of_model_descent_hypotheses
      (L_smooth := L_smooth) (f := f) (w := weightSequence w0 η z g_adv)
      (η := η) (z := z) (σsq := σsq) (ℱ := ℱ) (ℱfil := ℱfil) h_model
  exact ⟨h_step, h_core.1, h_core.2⟩

end LeanSharp
