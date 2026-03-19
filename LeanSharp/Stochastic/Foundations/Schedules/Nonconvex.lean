/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Foundations.Schedules.StronglyConvex

/-!
# Non-Convex Schedules

This module exists to isolate the non-convex and z-score non-convex rate bounds
that build on `weightSequence`, keeping non-convex telescoping and algebraic
rearrangement lemmas in a dedicated unit.

## Theorems

* `zsharp_nonconvex_rate`: `O(1/√T)` bound for average gradient norm squared.
* `z_score_nonconvex_rate_complete`: z-score non-convex rate bound.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

private lemma nonconvex_telescoping_descent (L : W ι → ℝ) (w0 : W ι)
    (z L_smooth σsq η0 : ℝ)
    (η : ℕ → ℝ) (h_step : ∀ t, η t = η0) (g_adv : ℕ → Ω → W ι) (T : ℕ)
    (h_L_descent : ∀ t, 𝔼[fun ω => L (weightSequence w0 η z g_adv (t + 1) ω)] ≤
        𝔼[fun ω => L (weightSequence w0 η z g_adv t ω)] -
        (η t / 2) * 𝔼[fun ω => ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2] +
        ((η t) ^ 2 * L_smooth / 2) * σsq) :
    (η0 / 2) * (∑ t ∈ Finset.range T,
      𝔼[fun ω => ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2])
      ≤ (L w0 - 𝔼[fun ω => L (weightSequence w0 η z g_adv T ω)]) +
        (T : ℝ) * (η0^2 * L_smooth / 2) * σsq := by
  calc (η0 / 2) * (∑ t ∈ Finset.range T,
      𝔼[fun ω => ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2])
    _ = ∑ t ∈ Finset.range T, (η0 / 2) *
        𝔼[fun ω => ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2] :=
          by rw [Finset.mul_sum]
    _ ≤ ∑ t ∈ Finset.range T, (𝔼[fun ω => L (weightSequence w0 η z g_adv t ω)] -
        𝔼[fun ω => L (weightSequence w0 η z g_adv (t + 1) ω)] +
        (η0 ^ 2 * L_smooth / 2) * σsq) :=
      Finset.sum_le_sum (fun t _ => by have h := h_L_descent t; rw [h_step t] at h; linarith)
    _ = (∑ t ∈ Finset.range T, (𝔼[fun ω => L (weightSequence w0 η z g_adv t ω)] -
        𝔼[fun ω => L (weightSequence w0 η z g_adv (t + 1) ω)])) +
        (∑ t ∈ Finset.range T, (η0 ^ 2 * L_smooth / 2) * σsq) := Finset.sum_add_distrib
    _ = (𝔼[fun ω => L (weightSequence w0 η z g_adv 0 ω)] -
        𝔼[fun ω => L (weightSequence w0 η z g_adv T ω)]) +
        (T : ℝ) * (η0 ^ 2 * L_smooth / 2) * σsq := by
      rw [Finset.sum_range_sub' (fun t => 𝔼[fun ω => L (weightSequence w0 η z g_adv t ω)])]
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      ring
    _ = (L w0 - 𝔼[fun ω => L (weightSequence w0 η z g_adv T ω)]) +
        (T : ℝ) * (η0 ^ 2 * L_smooth / 2) * σsq := by
      have h_init : (fun ω => L (weightSequence w0 η z g_adv 0 ω)) = fun _ => L w0 := by
        ext ω; rw [weightSequence]
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
    (h_bdd : BddBelow (Set.range L))
    (h_int_L : ∀ t, Integrable (fun ω => L (weightSequence w0 η z g_adv t ω)))
    (h_L_descent : ∀ t, 𝔼[fun ω => L (weightSequence w0 η z g_adv (t + 1) ω)] ≤
        𝔼[fun ω => L (weightSequence w0 η z g_adv t ω)] -
        (η t / 2) * 𝔼[fun ω => ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2] +
        ((η t) ^ 2 * L_smooth / 2) * σsq) :
    (1 / (T : ℝ)) * (∑ t ∈ Finset.range T,
      𝔼[fun ω => ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2])
      ≤ (2 * (L w0 - sInf (Set.range L)) + L_smooth * σsq) / Real.sqrt (T : ℝ) := by
  let S := ∑ t ∈ Finset.range T,
      𝔼[fun ω => ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2]
  let η0 := η 0
  have h_eta : ∀ t, η t = η 0 := fun t => by rw [h_step t, h_step 0]
  have h_telescope := nonconvex_telescoping_descent L w0 z L_smooth σsq (η 0) η
      h_eta g_adv T h_L_descent
  have h_inf : sInf (Set.range L) ≤ 𝔼[fun ω => L (weightSequence w0 η z g_adv T ω)] := by
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
    (h_int_L : ∀ t, Integrable (fun ω => L (weightSequence w0 η z g_adv t ω)))
    (h_int_grad : ∀ t, Integrable
      (fun ω => ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2) ℙ)
    (h_desc : ∀ t, ∀ᵐ ω ∂ℙ,
      volume[fun ω' => L (stochasticZSharpStep
        (weightSequence w0 η z g_adv t ω') η t z (g_adv t) ω') | ℱ t] ω ≤
      L (weightSequence w0 η z g_adv t ω) - (η t / 4) *
        ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2 +
      ((η t) ^ 2 * L_smooth / 2) * σsq)
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace) :
    (1 / (T : ℝ)) * (∑ t ∈ Finset.range T,
      𝔼[fun ω => ‖gradient L (weightSequence w0 η z g_adv t ω)‖ ^ 2])
      ≤ (8 * L_smooth * (L w0 - sInf (Set.range L)) + σsq) / Real.sqrt (T : ℝ) := by
  let W_seq (t : ℕ) (ω : Ω) := weightSequence w0 η z g_adv t ω
  have h_step_seq (t : ℕ) : ∀ᵐ ω ∂ℙ, W_seq (t + 1) ω =
      stochasticZSharpStep (W_seq t ω) η t z (g_adv t) ω := by
    apply Filter.Eventually.of_forall; intro ω; dsimp only [W_seq]; rw [weightSequence]
  have h_sequence_desc := LeanSharp.stochastic_zsharp_sequence_descent
    L_smooth L W_seq η z σsq T g_adv ℱ h_step_seq h_desc h_int_L h_int_grad h_meas
  have h_eta_iden : ∀ t, η t = η 0 := fun t => by rw [h_step t, h_step 0]
  have h_sequence_desc_fixed : (η 0 / 4) * (∑ t ∈ Finset.range T,
      𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) ≤
      𝔼[fun ω => L (W_seq 0 ω)] - 𝔼[fun ω => L (W_seq T ω)] +
      (∑ t ∈ Finset.range T, η t ^ 2 * L_smooth / 2 * σsq) := by
    rw [Finset.mul_sum]
    have h_eq : (∑ t ∈ Finset.range T,
          (η 0 / 4) * 𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) =
        (∑ t ∈ Finset.range T,
          (η t / 4) * 𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) := by
      apply Finset.sum_congr rfl; intro t _; rw [h_eta_iden t]
    rw [h_eq]; exact h_sequence_desc
  have h_inf : sInf (Set.range L) ≤ 𝔼[fun ω => L (W_seq T ω)] := by
    have h_le := integral_mono (integrable_const (sInf (Set.range L))) (h_int_L T)
        (fun ω => csInf_le h_bdd (Set.mem_range_self (W_seq T ω)))
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h_le
    exact h_le
  have hT_pos : (T : ℝ) > 0 := by norm_cast
  have h_rearrange := z_score_rate_rearrangement T hT (η 0)
    (∑ t ∈ Finset.range T, 𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2]) L_smooth σsq
    (L w0 - 𝔼[fun ω => L (W_seq T ω)]) h_L_pos (h_step 0)
  apply (h_rearrange ?_).trans
  · apply div_le_div_of_nonneg_right _ (Real.sqrt_pos.mpr hT_pos).le
    nlinarith [h_inf, csInf_le h_bdd (Set.mem_range_self w0)]
  · calc (η 0 / 4) * (∑ t ∈ Finset.range T, 𝔼[fun ω => ‖gradient L (W_seq t ω)‖ ^ 2])
      _ ≤ 𝔼[fun ω => L (W_seq 0 ω)] - 𝔼[fun ω => L (W_seq T ω)] +
          (∑ t ∈ Finset.range T, η t ^ 2 * L_smooth / 2 * σsq) := h_sequence_desc_fixed
      _ = (L w0 - 𝔼[fun ω => L (W_seq T ω)]) +
          (T : ℝ) * (η 0 ^ 2 * L_smooth / 2) * σsq := by
          have h0 : (fun ω => L (W_seq 0 ω)) = fun _ => L w0 := by
            ext ω; dsimp only [W_seq]; rw [weightSequence]
          rw [h0, integral_const, probReal_univ, one_smul]
          congr 1
          rw [Finset.sum_congr rfl (fun t _ => by rw [h_eta_iden t]),
              Finset.sum_const, nsmul_eq_mul, Finset.card_range]
          ring

end LeanSharp
