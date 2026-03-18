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

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- Recursively define the weight iterates for ZSharp. -/
noncomputable def weight_sequence (w0 : W ι) (η : ℕ → ℝ) (z : ℝ)
    (g_adv : ℕ → Ω → W ι) : ℕ → Ω → W ι
| 0, _ => w0
| t+1, ω => stochastic_zsharp_step (weight_sequence w0 η z g_adv t ω) η t z (g_adv t) ω

/-- **Strongly Convex Induction Step**: The $T \to T+1$ recursion for the $O(1/T)$ rate. -/
private lemma strongly_convex_induction_step (t : ℕ) (μ C : ℝ) (η : ℕ → ℝ)
    (w_star w0 : W ι) (g_adv : ℕ → Ω → W ι) (ℱ : ℕ → MeasurableSpace Ω)
    (h_le : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_cond_bound : ∀ t, ∀ᵐ ω ∂volume,
      volume[fun ω' =>
        ‖weight_sequence w0 η z g_adv (t + 1) ω' - w_star‖ ^ 2 | ℱ t] ω ≤
      (1 - η t * μ) * ‖weight_sequence w0 η z g_adv t ω - w_star‖ ^ 2)
    (h_int : ∀ t, Integrable (fun ω => ‖weight_sequence w0 η z g_adv t ω - w_star‖ ^ 2))
    (h_ih : 𝔼[fun ω => ‖weight_sequence w0 η z g_adv t ω - w_star‖ ^ 2] ≤ C / t)
    (h_step : η t = 1 / (μ * (t + 1))) (hμ : μ > 0) (ht : 0 < t) :
    𝔼[fun ω => ‖weight_sequence w0 η z g_adv (t + 1) ω - w_star‖ ^ 2] ≤
      C / (t + 1) := by
  have h_contraction_factor : 1 - (η t) * μ = (t : ℝ) / (t + 1) := by
    rw [h_step]; field_simp [hμ.ne']; ring
  have h_iter : 𝔼[fun ω => ‖weight_sequence w0 η z g_adv (t + 1) ω - w_star‖ ^ 2] ≤
      ((t : ℝ) / (t + 1)) *
        𝔼[fun ω => ‖weight_sequence w0 η z g_adv t ω - w_star‖ ^ 2] := by
    rw [(integral_condExp (h_le t)).symm]
    apply le_trans (integral_mono_ae integrable_condExp
      (Integrable.const_mul (h_int t) (1 - η t * μ)) (h_cond_bound t))
    rw [integral_const_mul, h_contraction_factor]
  calc 𝔼[fun ω => ‖weight_sequence w0 η z g_adv (t + 1) ω - w_star‖ ^ 2]
    _ ≤ ((t : ℝ) / (t + 1)) *
        𝔼[fun ω => ‖weight_sequence w0 η z g_adv t ω - w_star‖ ^ 2] := h_iter
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
        ‖weight_sequence w0 η z g_adv (t + 1) ω' - w_star‖ ^ 2 | ℱ t] ω ≤
      (1 - η t * μ) * ‖weight_sequence w0 η z g_adv t ω - w_star‖ ^ 2)
    (hμ : 0 < μ)
    (h_step : ∀ t, η t = 1 / (μ * (t + 1)))
    (h_align0 : stochastic_alignment_condition w_star w0 η 0 z μ (g_adv 0))
    (h_int : ∀ t, Integrable (fun ω => ‖weight_sequence w0 η z g_adv t ω - w_star‖ ^ 2)) :
    ∃ C : ℝ, ∀ T : ℕ, T > 0 →
      𝔼[fun ω => ‖weight_sequence w0 η z g_adv T ω - w_star‖ ^ 2] ≤ C / T := by
  let C := ‖w0 - w_star‖ ^ 2 + 1
  use C
  intro T hT
  induction T with
  | zero => contradiction
  | succ t ih =>
    by_cases ht : t = 0
    · -- Base case T = 1
      rw [ht, Nat.cast_one, div_one]
      have h_bound : 𝔼[fun ω => ‖stochastic_zsharp_step w0 η 0 z (g_adv 0) ω - w_star‖ ^ 2] ≤
          (1 - (η 0) * μ) * ‖w0 - w_star‖ ^ 2 :=
        stochastic_zsharp_convergence w_star w0 η 0 z μ h_align0
      have h_zero : 1 - (η 0) * μ = 0 := by
        rw [h_step 0]; field_simp [hμ.ne']; ring
      rw [h_zero, zero_mul] at h_bound
      exact h_bound.trans (by linarith [pow_two_nonneg ‖w0 - w_star‖])
    · -- Inductive step T = t + 1
      have hval : C / ↑(t + 1) = C / (↑t + 1) := by norm_cast
      rw [hval]
      exact strongly_convex_induction_step t μ C η w_star w0 g_adv ℱ h_le h_cond_bound h_int
        (ih (Nat.pos_of_ne_zero ht)) (h_step t) hμ (Nat.pos_of_ne_zero ht)

private lemma nonconvex_telescoping_descent (L : W ι → ℝ) (w0 : W ι) (z L_smooth σsq η0 : ℝ)
    (η : ℕ → ℝ) (h_step : ∀ t, η t = η0) (g_adv : ℕ → Ω → W ι) (T : ℕ)
    (h_L_descent : ∀ t, 𝔼[fun ω => L (weight_sequence w0 η z g_adv (t + 1) ω)] ≤
        𝔼[fun ω => L (weight_sequence w0 η z g_adv t ω)] -
        (η t / 2) * 𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖ ^ 2] +
        ((η t) ^ 2 * L_smooth / 2) * σsq) :
    (η0 / 2) * (∑ t ∈ Finset.range T,
      𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖ ^ 2])
      ≤ (L w0 - 𝔼[fun ω => L (weight_sequence w0 η z g_adv T ω)]) +
        (T : ℝ) * (η0^2 * L_smooth / 2) * σsq := by
  calc (η0 / 2) *
      (∑ t ∈ Finset.range T, 𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖ ^ 2])
    _ = ∑ t ∈ Finset.range T, (η0 / 2) *
        𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖ ^ 2] := by rw [Finset.mul_sum]
    _ ≤ ∑ t ∈ Finset.range T, (𝔼[fun ω => L (weight_sequence w0 η z g_adv t ω)] -
        𝔼[fun ω => L (weight_sequence w0 η z g_adv (t + 1) ω)] +
        (η0 ^ 2 * L_smooth / 2) * σsq) :=
      Finset.sum_le_sum (fun t _ => by have h := h_L_descent t; rw [h_step t] at h; linarith)
    _ = (∑ t ∈ Finset.range T, (𝔼[fun ω => L (weight_sequence w0 η z g_adv t ω)] -
        𝔼[fun ω => L (weight_sequence w0 η z g_adv (t + 1) ω)])) +
        (∑ t ∈ Finset.range T, (η0 ^ 2 * L_smooth / 2) * σsq) := Finset.sum_add_distrib
    _ = (𝔼[fun ω => L (weight_sequence w0 η z g_adv 0 ω)] -
        𝔼[fun ω => L (weight_sequence w0 η z g_adv T ω)]) +
        (T : ℝ) * (η0 ^ 2 * L_smooth / 2) * σsq := by
      rw [Finset.sum_range_sub' (fun t => 𝔼[fun ω => L (weight_sequence w0 η z g_adv t ω)])]
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      ring
    _ = (L w0 - 𝔼[fun ω => L (weight_sequence w0 η z g_adv T ω)]) +
        (T : ℝ) * (η0 ^ 2 * L_smooth / 2) * σsq := by
      have h_init : (fun ω => L (weight_sequence w0 η z g_adv 0 ω)) = fun _ => L w0 := by
        ext ω; rw [weight_sequence]
      rw [h_init, integral_const, probReal_univ, one_smul]

/-- Auxiliary: the final algebraic rearrangement for the non-convex rate. -/
private lemma nonconvex_rate_rearrangement (T : ℕ) (hT : T > 0) (η0 S L_smooth σsq diff : ℝ)
    (h_eta : η0 = 1 / Real.sqrt (T : ℝ))
    (h_S_bdd : (η0 / 2) * S ≤ diff + (T : ℝ) * (η0 ^ 2 * L_smooth / 2) * σsq) :
    (1 / (T : ℝ)) * S ≤ (2 * diff + L_smooth * σsq) / Real.sqrt (T : ℝ) := by
  have hT_pos : (T : ℝ) > 0 := by norm_cast
  calc (1 / (T : ℝ)) * S = (2 / (T * η0)) * ((η0 / 2) * S)
    := by field_simp [h_eta, hT_pos.ne']
    _ ≤ (2 / (T * η0)) * (diff + T * (η0^2 * L_smooth / 2) * σsq) :=
        mul_le_mul_of_nonneg_left h_S_bdd (by rw [h_eta]; positivity)
    _ = (2 * diff + L_smooth * σsq) / Real.sqrt (T : ℝ) := by
        rw [h_eta]; field_simp [hT_pos]; rw [Real.sq_sqrt hT_pos.le]; ring

private lemma z_score_rate_rearrangement (T : ℕ) (hT : T > 0) (η0 S L_smooth σsq diff : ℝ)
    (hL : L_smooth > 0) (h_eta : η0 = 1 / (2 * L_smooth * Real.sqrt (T : ℝ)))
    (h_S_bdd : (η0 / 4) * S ≤ diff + (T : ℝ) * (η0 ^ 2 * L_smooth / 2) * σsq) :
    (1 / (T : ℝ)) * S ≤ (8 * L_smooth * diff + σsq) / Real.sqrt (T : ℝ) := by
  have hT_pos : (T : ℝ) > 0 := by norm_cast
  have h_eta_pos : η0 > 0 := by rw [h_eta]; positivity
  have h_eta_nz : η0 ≠ 0 := h_eta_pos.ne'
  field_simp [h_eta_nz, hT_pos.ne', hL.ne', (Real.sqrt_pos.mpr hT_pos).ne'] at h_S_bdd ⊢
  rw [h_eta] at *
  field_simp [hT_pos.ne', hL.ne', (Real.sqrt_pos.mpr hT_pos).ne'] at *
  rw [Real.sq_sqrt hT_pos.le] at *
  linarith

/-- **Non-convex Rate ($O(1/\sqrt{T})$)**:
For general smooth (but potentially non-convex) objectives, the average gradient
norm squared decreases at a rate of $1/\sqrt{T}$ given $\eta = 1/\sqrt{T}$. -/
theorem zsharp_nonconvex_rate (L : W ι → ℝ) (w0 : W ι) (z L_smooth σsq : ℝ)
    (η : ℕ → ℝ) (g_adv : ℕ → Ω → W ι) (T : ℕ) (hT : T > 0)
    (h_step : ∀ t, η t = 1 / Real.sqrt T)
    -- Objective function properties
    (h_bdd : BddBelow (Set.range L))
    (h_int_L : ∀ t, Integrable (fun ω => L (weight_sequence w0 η z g_adv t ω)))
    -- Landscape descent property (standard for L-smooth functions)
    (h_L_descent : ∀ t, 𝔼[fun ω => L (weight_sequence w0 η z g_adv (t + 1) ω)] ≤
        𝔼[fun ω => L (weight_sequence w0 η z g_adv t ω)] -
        (η t / 2) * 𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖ ^ 2] +
        ((η t) ^ 2 * L_smooth / 2) * σsq) :
    ∃ C : ℝ,
      (1 / (T : ℝ)) * (∑ t ∈ Finset.range T,
        𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖ ^ 2])
      ≤ C / Real.sqrt (T : ℝ) := by
  let C := 2 * (L w0 - sInf (Set.range L)) + L_smooth * σsq
  use C
  let S := ∑ t ∈ Finset.range T,
      𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖ ^ 2]
  let η0 := η 0
  have h_eta : ∀ t, η t = η 0 := fun t => by rw [h_step t, h_step 0]
  have h_telescope := nonconvex_telescoping_descent L w0 z L_smooth σsq (η 0) η
      h_eta g_adv T h_L_descent
  have h_inf : sInf (Set.range L) ≤ 𝔼[fun ω => L (weight_sequence w0 η z g_adv T ω)] := by
    have h_const : (𝔼[fun _ : Ω => sInf (Set.range L)]) = sInf (Set.range L) := by
      rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [← h_const]
    apply integral_mono (integrable_const _) (h_int_L T)
    intro ω; apply csInf_le h_bdd; apply Set.mem_range_self
  have h_rearrange_input : η 0 = 1 / Real.sqrt (T : ℝ) := h_step 0
  have h_S_bdd : (η 0 / 2) * S ≤ L w0 - sInf (Set.range L) + (T : ℝ)
      * (η 0 ^ 2 * L_smooth / 2) * σsq := by linarith
  exact nonconvex_rate_rearrangement T hT η0 S L_smooth σsq
    (L w0 - sInf (Set.range L)) h_rearrange_input h_S_bdd

theorem z_score_nonconvex_rate_complete (L : W ι → ℝ) (w0 : W ι) (z L_smooth σsq : ℝ)
    (η : ℕ → ℝ) (g_adv : ℕ → Ω → W ι) (T : ℕ) (hT : T > 0)
    (ℱ : ℕ → MeasurableSpace Ω)
    (h_step : ∀ t, η t = 1 / (2 * L_smooth * Real.sqrt T))
    (h_L_pos : L_smooth > 0)
    (h_bdd : BddBelow (Set.range L))
    (h_int_L : ∀ t, Integrable (fun ω => L (weight_sequence w0 η z g_adv t ω)))
    (h_int_grad : ∀ t, Integrable (fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖ ^ 2) ℙ)
    (h_desc : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => L (stochastic_zsharp_step
        (weight_sequence w0 η z g_adv t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      L (weight_sequence w0 η z g_adv t ω) - (η t / 4) *
        ‖gradient L (weight_sequence w0 η z g_adv t ω)‖ ^ 2 +
      ((η t) ^ 2 * L_smooth / 2) * σsq)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    ∃ C : ℝ,
      (1 / (T : ℝ)) * (∑ t ∈ Finset.range T,
        𝔼[fun ω => ‖gradient L (weight_sequence w0 η z g_adv t ω)‖ ^ 2])
      ≤ C / Real.sqrt (T : ℝ) := by
  let W_seq (t : ℕ) (ω : Ω) := weight_sequence w0 η z g_adv t ω
  have h_step_seq (t : ℕ) : ∀ᵐ ω ∂ℙ, W_seq (t + 1) ω =
      stochastic_zsharp_step (W_seq t ω) η t z (g_adv t) ω := by
    apply Filter.Eventually.of_forall; intro ω; dsimp only [W_seq]; rw [weight_sequence]
  have h_sequence_desc := LeanSharp.stochastic_zsharp_sequence_descent
    L_smooth L W_seq η z σsq T g_adv ℱ h_step_seq h_desc h_int_L h_int_grad h_meas
  have h_eta_iden : ∀ t, η t = η 0 := fun t => by rw [h_step t, h_step 0]
  have h_sequence_desc_fixed : (η 0 / 4) * (∑ t ∈ Finset.range T,
      𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) ≤
      𝔼[fun ω => L (W_seq 0 ω)] - 𝔼[fun ω => L (W_seq T ω)] +
      (∑ t ∈ Finset.range T, η t ^ 2 * L_smooth / 2 * σsq) := by
    rw [Finset.mul_sum]
    have h_eq : (∑ t ∈ Finset.range T, (η 0 / 4) * 𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) =
        (∑ t ∈ Finset.range T, (η t / 4) * 𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) := by
      apply Finset.sum_congr rfl; intro t _; rw [h_eta_iden t]
    rw [h_eq]; exact h_sequence_desc
  let C := 8 * L_smooth * (L w0 - sInf (Set.range L)) + σsq
  use C
  have h_inf : sInf (Set.range L) ≤ 𝔼[fun ω => L (W_seq T ω)] := by
    have h_le := integral_mono (integrable_const (sInf (Set.range L))) (h_int_L T)
        (fun ω => csInf_le h_bdd (Set.mem_range_self (W_seq T ω)))
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h_le
    exact h_le
  have hT_pos : (T : ℝ) > 0 := by norm_cast
  have η0_val : η 0 = 1 / (2 * L_smooth * Real.sqrt T) := h_step 0
  have h_rearrange := z_score_rate_rearrangement T hT (η 0)
    (∑ t ∈ Finset.range T, 𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) L_smooth σsq
    (L w0 - 𝔼[fun ω => L (W_seq T ω)]) h_L_pos (h_step 0)
  apply (h_rearrange ?_).trans
  · apply div_le_div_of_nonneg_right _ (Real.sqrt_pos.mpr hT_pos).le
    dsimp only [C]; nlinarith [h_inf, csInf_le h_bdd (Set.mem_range_self w0)]
  · calc (η 0 / 4) * (∑ t ∈ Finset.range T, 𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2])
      _ ≤ 𝔼[fun ω => L (W_seq 0 ω)] - 𝔼[fun ω => L (W_seq T ω)] +
          (∑ t ∈ Finset.range T, η t ^ 2 * L_smooth / 2 * σsq) := h_sequence_desc_fixed
      _ = (L w0 - 𝔼[fun ω => L (W_seq T ω)]) + (T : ℝ) * (η 0 ^ 2 * L_smooth / 2) * σsq := by
          have h0 : (fun ω => L (W_seq 0 ω)) = fun _ => L w0 := by
            ext ω; dsimp only [W_seq]; rw [weight_sequence]
          rw [h0, integral_const, probReal_univ, one_smul]
          congr 1
          rw [Finset.sum_congr rfl (fun t _ => by rw [h_eta_iden t]),
              Finset.sum_const, nsmul_eq_mul, Finset.card_range]
          ring

end LeanSharp
