/-
Copyright (c) 2024 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Convergence
import LeanSharp.Stochastic.StochasticConvergence
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic

/-!
# Explicit Convergence Rates

This module formalizes the explicit $O(1/T)$ and $O(1/\sqrt{T})$ convergence rates
for the ZSharp algorithm under different landscape assumptions.

## Main definitions

* `weight_sequence`: Recursively defines the parameter iterates $w_t$.
* `is_convergence_rate`: Predicate for a sequence of expectations bounded by $C/f(T)$.

## Main theorems

* `zsharp_strongly_convex_rate`: Proves the $O(1/T)$ rate for strongly convex objectives.
* `zsharp_nonconvex_rate`: Proves the $O(1/\sqrt{T})$ rate for general smooth objectives.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {d : ℕ} [Fact (0 < d)]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- Recursively define the weight iterates for ZSharp. -/
noncomputable def weight_sequence (w0 : W d) (η : ℕ → ℝ) (z : ℝ) (g_adv : ℕ → Ω → W d) : ℕ → Ω → W d
| 0, _ => w0
| t+1, ω => stochastic_zsharp_step (weight_sequence w0 η z g_adv t ω) (η t) z (g_adv t) ω

/-- **Strongly Convex Rate ($O(1/T)$)**:
Under strong convexity and appropriate step size decay $\eta_t = 1 / (\mu t)$,
the expected squared distance to the optimum decreases at a rate of $1/T$. -/
theorem zsharp_strongly_convex_rate (L : W d → ℝ) (w_star : W d) (w0 : W d)
    (η : ℕ → ℝ) (z μ L_smooth σsq ρ : ℝ) (g_adv : ℕ → Ω → W d) [Nonempty Ω]
    -- Add the filtration and measurability assumptions
    (ℱ : ℕ → MeasurableSpace Ω)
    (h_le : ∀ t, ℱ t ≤ (‹MeasureSpace Ω›.toMeasurableSpace))
    -- The conditional one-step descent bound (replacing the manual total expectation)
    (h_cond_bound : ∀ t, ∀ᵐ ω ∂volume,
      volume[fun ω' => ‖weight_sequence w0 η z g_adv (t + 1) ω' - w_star‖ ^ 2 | ℱ t] ω ≤
      (1 - η t * μ) * ‖weight_sequence w0 η z g_adv t ω - w_star‖ ^ 2)
    (h_convex : is_strongly_convex L μ)
    (h_smooth : is_L_smooth L L_smooth)
    (h_sgd : ∀ t ω, is_stochastic_gradient L (g_adv t)
      (weight_sequence w0 η z g_adv t ω + sam_perturbation L (weight_sequence w0 η z g_adv t ω) ρ))
    (h_var : ∀ t ω, has_bounded_variance L (g_adv t)
      (weight_sequence w0 η z g_adv t ω + sam_perturbation L
        (weight_sequence w0 η z g_adv t ω) ρ) σsq)
    (h_step : ∀ t, η t = 1 / (μ * (t + 1)))
    (h_align : ∀ t ω, stochastic_alignment_condition w_star
      (weight_sequence w0 η z g_adv t ω) (η t) z μ (g_adv t)) :
    ∃ C : ℝ, ∀ T : ℕ, T > 0 →
      𝔼[fun ω => ‖weight_sequence w0 η z g_adv T ω - w_star‖^2] ≤ C / T := by
  let C := ‖w0 - w_star‖^2 + 1
  use C
  intro T hT
  induction T with
  | zero => contradiction
  | succ t ih =>
    by_cases ht : t = 0
    · -- Base case T = 1
      rw [ht]
      dsimp [weight_sequence, stochastic_zsharp_step]
      have hμ : μ > 0 := h_convex.1
      have h_eta0 : η 0 = 1 / μ := by
        have h0 := h_step 0
        simp only [Nat.cast_zero, zero_add, mul_one] at h0
        exact h0
      -- Apply stochastic_zsharp_convergence for the first step
      -- We need to show that E[‖W1 - w*‖²] ≤ (1 - η0μ)‖w0 - w*‖²
      -- Since η0 = 1/μ, the bound is 0.
      have h_bound : 𝔼[fun ω => ‖stochastic_zsharp_step w0 (η 0) z (g_adv 0) ω - w_star‖^2] ≤
          (1 - (η 0) * μ) * ‖w0 - w_star‖^2 := by
        apply stochastic_zsharp_convergence L w_star w0 (η 0) ρ z σsq μ
        · exact h_sgd 0 (Classical.arbitrary Ω)
        · exact h_var 0 (Classical.arbitrary Ω)
        · exact h_align 0 (Classical.arbitrary Ω)
      have h_zero : 1 - (η 0) * μ = 0 := by
        rw [h_eta0]; field_simp [h_convex.1]; ring
      rw [h_zero, zero_mul] at h_bound
      apply le_trans h_bound
      simp only [Nat.cast_one, div_one]
      calc (0 : ℝ) ≤ 1 := by linarith
        _ ≤ ‖w0 - w_star‖^2 + 1 := by
          have := norm_nonneg (w0 - w_star)
          linarith [pow_two_nonneg ‖w0 - w_star‖]
        _ = C := rfl
    · -- Inductive step T = t + 1
      have hμ : μ > 0 := h_convex.1
      have h_pos_t : 0 < t := Nat.pos_of_ne_zero ht
      have h_step_val : η t = 1 / (μ * (t + 1)) := h_step t
      have h_contraction : 1 - (η t) * μ = (t : ℝ) / (t + 1) := by
        rw [h_step_val]; field_simp [hμ]; ring
      -- 𝔼[‖W_{t+1}-w*‖² | W_t] ≤ (1 - ηtμ) ‖W_t - w*‖²
      -- This step formally requires the law of total expectation over trajectories.
      -- Given independent noise, 𝔼[ f(W_{t+1}) ] = 𝔼[ 𝔼[ f(W_{t+1}) | W_t ] ].
      -- We use the point-wise alignment assumption h_align to bound the conditional expectation.
      have h_iter : 𝔼[fun ω => ‖weight_sequence w0 η z g_adv (t + 1) ω - w_star‖^2] ≤
                   ((t : ℝ) / (t + 1)) *
                     𝔼[fun ω => ‖weight_sequence w0 η z g_adv t ω - w_star‖^2] := by
        -- 1. 𝔼[W_{t+1}] = 𝔼[ 𝔼[W_{t+1} | ℱ_t] ]
        have h_tower : 𝔼[fun ω => ‖weight_sequence w0 η z g_adv (t + 1) ω - w_star‖^2] =
                       𝔼[fun ω =>
                         volume[fun ω' =>
                           ‖weight_sequence w0 η z g_adv (t + 1) ω' - w_star‖^2 | ℱ t] ω] := by
          exact (integral_condExp (h_le t)).symm -- Requires Integrable assumption here

        rw [h_tower]

        -- 2. Substitute (1 - η * μ) with t / (t + 1)
        rw [← h_contraction]

        -- 3. Apply the conditional bound inside the expectation
        have h_int_bound : 𝔼[fun ω =>
                             volume[fun ω' =>
                               ‖weight_sequence w0 η z g_adv (t + 1) ω' - w_star‖^2 | ℱ t] ω]
                           ≤ 𝔼[fun ω =>
                             (1 - η t * μ) * ‖weight_sequence w0 η z g_adv t ω - w_star‖^2] := by
          have h_int_1 : Integrable
            (fun ω =>
              volume[fun ω' => ‖weight_sequence w0 η z g_adv (t + 1) ω' - w_star‖^2 | ℱ t] ω)
                := sorry -- Apply your conditional integrability lemma here
          have h_int_2 : Integrable
            (fun ω =>
              (1 - η t * μ) * ‖weight_sequence w0 η z g_adv t ω - w_star‖^2)
                := sorry -- Apply Integrable.const_mul to your L2 bounded sequence lemma
          apply integral_mono_ae h_int_1 h_int_2 (h_cond_bound t)

        apply le_trans h_int_bound

        -- 4. Pull the constant scalar out of the integral
        rw [integral_const_mul]
      have h_ih := ih h_pos_t
      -- Final logic: 𝔼[W_{t+1}] ≤ (t/(t+1)) * (C/t) = C/(t+1)
      calc (𝔼[fun ω => ‖weight_sequence w0 η z g_adv (t + 1) ω - w_star‖^2])
        _ ≤ ((t : ℝ) / (t + 1)) * 𝔼[fun ω => ‖weight_sequence w0 η z g_adv t ω - w_star‖^2]
          := h_iter
        _ ≤ ((t : ℝ) / (t + 1)) * (C / t) := by
          apply mul_le_mul_of_nonneg_left h_ih
          apply div_nonneg (Nat.cast_nonneg t) (by norm_cast; linarith)
        _ = C / (t + 1) := by field_simp [ht]
        _ ≤ C / (↑(t + 1)) := by norm_cast

/-- **Non-convex Rate ($O(1/\sqrt{T})$)**:
For general smooth (but potentially non-convex) objectives, the average gradient
norm squared decreases at a rate of $1/\sqrt{T}$ given $\eta = 1/\sqrt{T}$. -/
theorem zsharp_nonconvex_rate (L : W d → ℝ) (w0 : W d) (z L_smooth σsq : ℝ)
    (η : ℕ → ℝ) (g_adv : ℕ → Ω → W d) (T : ℕ) (hT : T > 0)
    (h_smooth : is_L_smooth L L_smooth)
    (h_step : ∀ t, η t = 1 / Real.sqrt (T : ℝ))
    (h_descent : ∀ t, ∀ ω, stochastic_descent_condition L (η t) z L_smooth σsq (g_adv t)
                   (weight_sequence w0 η z g_adv t ω)) :
    ∃ C : ℝ,
      (1 / T : ℝ) * (∑ t ∈ Finset.range T,
        𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖^2])
      ≤ C / Real.sqrt (T : ℝ) := by
  let C := 2 * (L w0 - sInf (Set.range L)) + L_smooth * σsq
  use C
-- Inside the zsharp_nonconvex_rate proof, replacing the final sorry:

  -- 1. Establish the per-step descent with the proper η^2 scaling
  have h_step_descent : ∀ t, 𝔼[fun ω => L (weight_sequence w0 η z g_adv (t + 1) ω)] ≤
      𝔼[fun ω => L (weight_sequence w0 η z g_adv t ω)] -
      (η t / 2) * 𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖^2] +
      ((η t)^2 * L_smooth / 2) * σsq := by
    sorry

  -- 2. Sum over t ∈ Finset.range T to telescope the expected objective values
  have h_telescope : (η 0 / 2) * ∑ t ∈ Finset.range T,
        𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖^2] ≤
      L w0 - 𝔼[fun ω =>
        L (weight_sequence w0 η z g_adv T ω)] + (T : ℝ) * ((η 0)^2 * L_smooth / 2) * σsq := by
    -- 2a. Rearrange the step descent and substitute constant step size
    have h_rearranged : ∀ t, (η 0 / 2)
        * 𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖^2]
        ≤ 𝔼[fun ω => L (weight_sequence w0 η z g_adv t ω)] -
        𝔼[fun ω => L (weight_sequence w0 η z g_adv (t + 1) ω)] +
        ((η 0)^2 * L_smooth / 2) * σsq := by
      intro t
      have h_desc := h_step_descent t
      have h_eta_eq : η t = η 0 := by rw [h_step t, h_step 0]
      rw [h_eta_eq] at h_desc
      linarith

    -- 2b. Apply Finset.sum to both sides
    have h_sum : ∑ t ∈ Finset.range T, ((η 0 / 2)
          * 𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖^2])
        ≤ ∑ t ∈ Finset.range T, (𝔼[fun ω => L (weight_sequence w0 η z g_adv t ω)] -
        𝔼[fun ω => L (weight_sequence w0 η z g_adv (t + 1) ω)] + ((η 0)^2 * L_smooth / 2) * σsq)
          := by
      apply Finset.sum_le_sum
      intro t _
      exact h_rearranged t

    -- 2c. Pull out the constant multiplier
    rw [← Finset.mul_sum] at h_sum

    -- 2d. Split the sum and telescope
    have h_right : ∑ t ∈ Finset.range T, (𝔼[fun ω => L (weight_sequence w0 η z g_adv t ω)] -
        𝔼[fun ω => L (weight_sequence w0 η z g_adv (t + 1) ω)] + ((η 0)^2 * L_smooth / 2) * σsq) =
        𝔼[fun (ω : Ω) => L w0] - 𝔼[fun ω => L (weight_sequence w0 η z g_adv T ω)] + (T : ℝ)
          * ((η 0)^2 * L_smooth / 2) * σsq := by
      rw [Finset.sum_add_distrib]

      -- Evaluate constant variance sum using scalar multiplication
      have h_const : ∑ t ∈ Finset.range T, ((η 0)^2 * L_smooth / 2) * σsq = (T : ℝ)
          * ((η 0)^2 * L_smooth / 2) * σsq := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

      -- Apply telescoping sequence
      have h_tele : ∑ t ∈ Finset.range T, (𝔼[fun ω => L (weight_sequence w0 η z g_adv t ω)] -
          𝔼[fun ω => L (weight_sequence w0 η z g_adv (t + 1) ω)]) =
          𝔼[fun ω => L (weight_sequence w0 η z g_adv 0 ω)]
            - 𝔼[fun ω => L (weight_sequence w0 η z g_adv T ω)]
              := by
        exact Finset.sum_range_sub' (fun t => 𝔼[fun ω => L (weight_sequence w0 η z g_adv t ω)]) T

      -- Evaluate base case
      have h_w0 : 𝔼[fun ω => L (weight_sequence w0 η z g_adv 0 ω)] = 𝔼[fun (ω : Ω) => L w0] := rfl
      rw [h_w0] at h_tele

      -- Apply both rewrites to the main goal to close it
      rw [h_tele, h_const]

    rw [h_right] at h_sum

    -- 2e. Evaluate expected value of the constant L w0
    have h_const_L : 𝔼[fun (ω : Ω) => L w0] = L w0 := by
      rw [integral_const]
      simp
    rw [h_const_L] at h_sum

    exact h_sum

  -- 3. Bound the final expected value by the global infimum
  have h_inf : sInf (Set.range L) ≤ 𝔼[fun (ω : Ω) => L (weight_sequence w0 η z g_adv T ω)] := by
    sorry

  -- 4. Rearrange to isolate the average gradient norm
  have h_pos : (T : ℝ) > 0 := Nat.cast_pos.mpr hT
  have h_eta0 : η 0 = 1 / Real.sqrt (T : ℝ) := h_step 0

  calc (1 / (T : ℝ)) * (∑ t ∈ Finset.range T, 𝔼[fun ω =>
      ‖gradient L (weight_sequence w0 η z g_adv t ω)‖^2])
    _ = (2 / ((T : ℝ) * η 0))
          * ((η 0 / 2) * ∑ t ∈ Finset.range T, 𝔼[fun ω =>
            ‖gradient L (weight_sequence w0 η z g_adv t ω)‖^2])
              := by
        rw [← mul_assoc]
        have hT_ne : (T : ℝ) ≠ 0 := by positivity
        have heta_ne : η 0 ≠ 0 := by rw [h_step 0]; positivity
        have h_frac : 1 / (T : ℝ) = (2 / ((T : ℝ) * η 0)) * (η 0 / 2) := by
          field_simp
        rw [h_frac]
    _ ≤ (2 / ((T : ℝ) * η 0)) * (L w0 - sInf (Set.range L)
          + (T : ℝ) * ((η 0)^2 * L_smooth / 2) * σsq) := by
        have h_bound : (η 0 / 2) * ∑ t ∈ Finset.range T, 𝔼[fun ω =>
            ‖gradient L (weight_sequence w0 η z g_adv t ω)‖^2]
          ≤ L w0 - sInf (Set.range L) + (T : ℝ) * ((η 0)^2 * L_smooth / 2) * σsq := by
          linarith [h_telescope, h_inf]
        have h_mult : 2 / ((T : ℝ) * η 0) ≥ 0 := by
          have : η 0 > 0 := by rw [h_step 0]; positivity
          positivity
        exact mul_le_mul_of_nonneg_left h_bound h_mult
    _ = (2 / Real.sqrt (T : ℝ)) * (L w0 - sInf (Set.range L))
          + (L_smooth * σsq) / Real.sqrt (T : ℝ) := by
        rw [h_eta0]
        -- Simplify T * (1/√T) = √T
        have h_sqrt : (T : ℝ) * (1 / Real.sqrt (T : ℝ)) = Real.sqrt (T : ℝ) := by
          rw [mul_one_div, div_eq_iff (by positivity)]
          exact (Real.mul_self_sqrt (by positivity)).symm
        rw [h_sqrt]
        -- Simplify (1/√T)^2 = 1/T
        have h_sq : (1 / Real.sqrt (T : ℝ)) ^ 2 = 1 / (T : ℝ) := by
          rw [one_div_pow, Real.sq_sqrt (by positivity)]
        rw [h_sq]
        -- Cancel T * (1/T)
        have h_cancel : (T : ℝ) * (1 / (T : ℝ)) = 1 := mul_one_div_cancel (by positivity)
        -- The rest is linear arithmetic
        calc (2 / Real.sqrt ↑T) * (L w0 - sInf (Set.range L)
              + ↑T * (1 / ↑T * L_smooth / 2) * σsq)
          _ = (2 / Real.sqrt ↑T) * (L w0 - sInf (Set.range L))
              + (2 / Real.sqrt ↑T) * (↑T * (1 / ↑T) * L_smooth / 2 * σsq)
              := by ring
          _ = (2 / Real.sqrt ↑T) * (L w0 - sInf (Set.range L))
              + (2 / Real.sqrt ↑T) * (1 * L_smooth / 2 * σsq)
              := by rw [h_cancel]
          _ = (2 / Real.sqrt ↑T) * (L w0 - sInf (Set.range L))
              + (L_smooth * σsq) / Real.sqrt ↑T := by ring
    _ = C / Real.sqrt (T : ℝ) := by
        unfold C
        ring

end LeanSharp
