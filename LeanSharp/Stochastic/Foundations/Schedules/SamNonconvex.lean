/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Process.Sequence
import LeanSharp.Stochastic.Foundations.Schedules.Nonconvex

/-!
# SAM Non-Convex Schedules

This module connects the conditional SAM descent envelope to the complete
finite-horizon non-convex rate.

## Main Theorems
* `sam_nonconvex_rate_complete`: Conditional SAM envelope implies an
  `O(1/√T)` average-gradient rate.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

private lemma sam_rate_rearrangement (T : ℕ) (hT : T > 0)
    (η0 S L_smooth C diff : ℝ) (hL : L_smooth > 0)
    (h_eta : η0 = 1 / (2 * L_smooth * Real.sqrt (T : ℝ)))
    (h_S_bdd : (η0 / 4) * S ≤
      diff + (T : ℝ) * (η0 ^ 2 * L_smooth / 2) * C) :
    (1 / (T : ℝ)) * S ≤ (8 * L_smooth * diff + C) / Real.sqrt (T : ℝ) := by
  have hT_pos : (T : ℝ) > 0 := by norm_cast
  have h_eta_pos : η0 > 0 := by rw [h_eta]; positivity
  have h_eta_nz : η0 ≠ 0 := h_eta_pos.ne'
  field_simp [h_eta_nz, hT_pos.ne', hL.ne', (Real.sqrt_pos.mpr hT_pos).ne'] at h_S_bdd ⊢
  rw [h_eta] at *
  field_simp [hT_pos.ne', hL.ne', (Real.sqrt_pos.mpr hT_pos).ne'] at *
  rw [Real.sq_sqrt hT_pos.le] at *
  linarith

/-- **Complete SAM Non-Convex Rate ($O(1/\sqrt{T})$)**:
Under the conditional SAM descent envelope, the average gradient norm squared
is bounded by the usual non-convex rate plus the explicit perturbation penalty
`2L²ρ²`. -/
theorem sam_nonconvex_rate_complete
    (L : W ι → ℝ) (w0 : W ι) (z L_smooth σsq ρ : ℝ)
    (η : ℕ → ℝ) (g_adv : ℕ → Ω → W ι) (T : ℕ) (hT : T > 0)
    (ℱ : ℕ → MeasurableSpace Ω)
    (h_step : ∀ t, η t = 1 / (2 * L_smooth * Real.sqrt T))
    (h_L_pos : L_smooth > 0)
    (h_bdd : BddBelow (Set.range L))
    (h_int_L : ∀ t, Integrable
      (fun ω => L (weightSequence w0 η z g_adv t ω)))
    (h_int_grad : ∀ t, Integrable
      (fun ω => ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2) ℙ)
    (h_desc : ∀ t, SAMDescentEnvelope L_smooth L
      (weightSequence w0 η z g_adv) η z σsq ρ g_adv ℱ t)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    (1 / (T : ℝ)) * (∑ t ∈ Finset.range T,
      𝔼[fun ω => ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2])
      ≤ (8 * L_smooth * (L w0 - sInf (Set.range L)) +
        (σsq + 2 * L_smooth ^ 2 * ρ ^ 2)) / Real.sqrt (T : ℝ) := by
  let W_seq (t : ℕ) (ω : Ω) := weightSequence w0 η z g_adv t ω
  have h_step_seq (t : ℕ) : ∀ᵐ ω ∂ℙ,
      W_seq (t + 1) ω = stochasticZSharpStep (W_seq t ω) η t z (g_adv t) ω := by
    apply Filter.Eventually.of_forall
    intro ω
    dsimp only [W_seq]
    rw [weightSequence]
  have h_sequence_desc := sam_sequence_descent L_smooth L W_seq η z σsq ρ T
    g_adv ℱ h_step_seq h_desc h_int_L h_int_grad h_meas
  have h_eta_iden : ∀ t, η t = η 0 := fun t => by rw [h_step t, h_step 0]
  have h_sequence_desc_fixed : (η 0 / 4) *
      (∑ t ∈ Finset.range T, 𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) ≤
      𝔼[fun ω => L (W_seq 0 ω)] - 𝔼[fun ω => L (W_seq T ω)] +
      (T : ℝ) * (η 0 ^ 2 * L_smooth / 2) *
        (σsq + 2 * L_smooth ^ 2 * ρ ^ 2) := by
    rw [Finset.mul_sum]
    calc
      (∑ t ∈ Finset.range T, (η 0 / 4) *
          𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) ≤
          𝔼[fun ω => L (W_seq 0 ω)] - 𝔼[fun ω => L (W_seq T ω)] +
            (∑ t ∈ Finset.range T, (η t ^ 2 * L_smooth / 2) *
              (σsq + 2 * L_smooth ^ 2 * ρ ^ 2)) := by
        have h_coeff : (∑ t ∈ Finset.range T, (η 0 / 4) *
            𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) =
            ∑ t ∈ Finset.range T, (η t / 4) *
              𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2] := by
          apply Finset.sum_congr rfl
          intro t _
          rw [h_eta_iden t]
        rw [h_coeff]
        exact h_sequence_desc
      _ = 𝔼[fun ω => L (W_seq 0 ω)] - 𝔼[fun ω => L (W_seq T ω)] +
            (T : ℝ) * (η 0 ^ 2 * L_smooth / 2) *
              (σsq + 2 * L_smooth ^ 2 * ρ ^ 2) := by
        rw [Finset.sum_congr rfl (fun t _ => by rw [h_eta_iden t]),
          Finset.sum_const, nsmul_eq_mul, Finset.card_range]
        ring
  have h_inf : sInf (Set.range L) ≤ 𝔼[fun ω => L (W_seq T ω)] := by
    have h_int_seq : Integrable (fun ω => L (W_seq T ω)) ℙ := by
      simpa only [W_seq] using h_int_L T
    have h_le := integral_mono (integrable_const (sInf (Set.range L))) h_int_seq
      (fun ω => csInf_le h_bdd (Set.mem_range_self (W_seq T ω)))
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h_le
    exact h_le
  have h_init : (fun ω => L (W_seq 0 ω)) = fun _ => L w0 := by
    ext ω
    dsimp only [W_seq]
    rw [weightSequence]
  have h_s_bdd : (η 0 / 4) *
      (∑ t ∈ Finset.range T, 𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) ≤
      L w0 - sInf (Set.range L) + (T : ℝ) *
        (η 0 ^ 2 * L_smooth / 2) *
        (σsq + 2 * L_smooth ^ 2 * ρ ^ 2) := by
    rw [h_init, integral_const, probReal_univ, one_smul] at h_sequence_desc_fixed
    linarith [h_inf]
  exact sam_rate_rearrangement T hT (η 0)
    (∑ t ∈ Finset.range T, 𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2])
    L_smooth (σsq + 2 * L_smooth ^ 2 * ρ ^ 2)
    (L w0 - sInf (Set.range L)) h_L_pos (h_step 0) h_s_bdd

end LeanSharp
