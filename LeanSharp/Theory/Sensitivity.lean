/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Notation

set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

/-!
# Z-Score Sensitivity Analysis

This module formalizes the statistical sensitivity of the Z-score gradient filter.
We analyze how the threshold $z$ affects the probability of preserving significant
gradient components in the presence of stochastic noise.

## Main definitions

* `signal_noise_model`: A stochastic gradient model $g = g_{true} + \xi$.
* `preservation_event`: The event that a specific gradient component $i$ is preserved.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω]

/-- Stochastic model for gradient observations: $g(\omega) = g_{true} + \xi(\omega)$. -/
 structure SignalNoiseModel (ι : Type*) [Fintype ι] (Ω : Type*) [MeasureSpace Ω] where
  /-- The ground truth (true mean) of the signal. -/
  g_true : W ι
  /-- The zero-mean stochastic noise vector. -/
  noise : Ω → W ι
  h_mean : 𝔼[noise] = 0
  h_int : Integrable noise

/-- The observed stochastic gradient for a given model. -/
noncomputable def SignalNoiseModel.observed (m : SignalNoiseModel ι Ω) (ω : Ω) : W ι :=
  m.g_true + m.noise ω

/-- **Mean Stability**: Difference between observed and true mean is bounded by noise mean. -/
lemma vector_mean_stability (m : SignalNoiseModel ι Ω) (ω : Ω) [Nonempty ι] :
    |vector_mean (m.observed ω) - vector_mean m.g_true| ≤
    vector_mean (WithLp.equiv 2 _ |>.symm fun i => |(WithLp.equiv 2 _ (m.noise ω)) i|) := by
  have h_card : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have h_diff : vector_mean (m.observed ω) - vector_mean m.g_true = vector_mean (m.noise ω) := by
    dsimp only [SignalNoiseModel.observed, vector_mean]
    field_simp [h_card.ne.symm]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change (m.g_true i + m.noise ω i) - m.g_true i = m.noise ω i
    abel
  rw [h_diff, vector_mean, abs_div, abs_of_pos h_card]
  apply div_le_div_of_nonneg_right _ h_card.le
  exact Finset.abs_sum_le_sum_abs _ _

/-- Bounded variance assumption for the noise vector components. -/
def noise_variance_bound (m : SignalNoiseModel ι Ω) (σsq : ℝ) : Prop :=
  ∀ i : ι, 𝔼[fun ω => ((m.noise ω) i)^2] ≤ σsq

/-- **Noise Energy Bound**: The expectation of the squared norm of the noise vector. -/
lemma noise_expected_norm_sq (m : SignalNoiseModel ι Ω) (σsq : ℝ)
    (h_noise : noise_variance_bound m σsq)
    (h_int_sq : ∀ i, Integrable (fun ω => ((m.noise ω) i) ^ 2)) :
    𝔼[fun ω => ‖m.noise ω‖ ^ 2] ≤ Fintype.card ι * σsq := by
  dsimp only [noise_variance_bound, W] at *
  simp_rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [integral_finset_sum]
  · trans ∑ (_i : ι), σsq
    · apply Finset.sum_le_sum; intro i _; exact h_noise i
    · rw [Finset.sum_const, nsmul_eq_mul, Fintype.card]
  · intro i _; exact h_int_sq i

/-- The event that the $i$-th component is preserved by the Z-score filter. -/
def preservation_event (m : SignalNoiseModel ι Ω) (z : ℝ) (i : ι) : Set Ω :=
  {ω | |(WithLp.equiv 2 (ι → ℝ) (m.observed ω)) i - vector_mean (m.observed ω)| ≥
    z * vector_std (m.observed ω)}

/-- **Noise Norm Tail Bound**: Probability that noise norm exceeds a threshold. -/
lemma noise_norm_sq_tail_prob (m : SignalNoiseModel ι Ω) (σsq : ℝ) (l : ℝ) (hl : 0 < l)
    (h_noise : noise_variance_bound m σsq)
    (h_int_sq : ∀ i, Integrable (fun ω => ((m.noise ω) i) ^ 2)) :
    (volume {ω | ‖m.noise ω‖ ^ 2 ≥ l}).toReal ≤ (Fintype.card ι * σsq) / l := by
  have h_int_norm_sq : Integrable (fun ω => ‖m.noise ω‖ ^ 2) := by
    simp_rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    exact integrable_finset_sum _ (fun i _ => h_int_sq i)
  have h_markov := mul_meas_ge_le_integral_of_nonneg (μ := volume)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) h_int_norm_sq l
  trans 𝔼[fun ω => ‖m.noise ω‖ ^ 2] / l
  · rw [le_div_iff₀ hl, mul_comm]; exact h_markov
  · apply div_le_div_of_nonneg_right (noise_expected_norm_sq m σsq h_noise h_int_sq) hl.le

section Probability
variable [IsProbabilityMeasure (volume : Measure Ω)]

/-- The probability of the preservation event. -/
noncomputable def preservation_prob (m : SignalNoiseModel ι Ω) (z : ℝ) (i : ι) : ℝ :=
  (ℙ (preservation_event m z i)).toReal

/-- **Mean Deviation Bound**: The expectation of the error in vector mean is zero. -/
lemma vector_mean_observed_expected (m : SignalNoiseModel ι Ω) [Nonempty ι] :
    𝔼[fun ω => vector_mean (m.observed ω)] = vector_mean m.g_true := by
  dsimp only [SignalNoiseModel.observed, vector_mean]
  have h_card : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [MeasureTheory.integral_div]
  congr 1
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    have h_int_noise_i : Integrable (fun a => (WithLp.equiv 2 _ (m.noise a)) i) :=
      (EuclideanSpace.proj i : (W ι) →L[ℝ] ℝ).integrable_comp m.h_int
    rw [show ∫ a, (WithLp.equiv 2 _ (m.g_true + m.noise a)) i = ∫ a, (m.g_true i + (WithLp.equiv 2 _ (m.noise a)) i) by rfl]
    rw [MeasureTheory.integral_add (integrable_const _) h_int_noise_i]
    rw [integral_const]
    have h_zero : ∫ a, (WithLp.equiv 2 _ (m.noise a)) i = 0 := by
      change ∫ a, (EuclideanSpace.proj i : W ι →L[ℝ] ℝ) (m.noise a) = 0
      rw [ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i) m.h_int, m.h_mean, ContinuousLinearMap.map_zero]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, h_zero, add_zero]
    rfl
  · intro i _; exact (integrable_const _).add ((EuclideanSpace.proj i : (W ι) →L[ℝ] ℝ).integrable_comp m.h_int)

/-- **Z-Score Sensitivity Bound**:
If the noise energy is bounded, the component is preserved with high probability
provided the signal strength is sufficient (captured by `h_impl`). -/
theorem preservation_prob_lower_bound (m : SignalNoiseModel ι Ω) (z : ℝ) (i : ι)
    (σ_sq : ℝ) (h_noise : noise_variance_bound m σ_sq)
    (h_int_sq : ∀ i, Integrable (fun ω => ((m.noise ω) i) ^ 2))
    (threshold : ℝ) (h_t : 0 < threshold)
    (h_impl : ∀ ω, ‖m.noise ω‖ ^ 2 < threshold → ω ∈ preservation_event m z i) :
    preservation_prob m z i ≥ 1 - (Fintype.card ι * σ_sq / threshold) := by
  simp only [preservation_prob]
  have h_mono : (ℙ {ω | ‖m.noise ω‖ ^ 2 < threshold}).toReal ≤ (ℙ (preservation_event m z i)).toReal :=
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr (measure_mono h_impl)
  have h_tail := noise_norm_sq_tail_prob m σ_sq threshold h_t h_noise h_int_sq
  have h_sum : (ℙ {ω | ‖m.noise ω‖ ^ 2 < threshold}).toReal + (ℙ {ω | ‖m.noise ω‖ ^ 2 ≥ threshold}).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top ℙ _) (measure_ne_top ℙ _)]
    · have h_int_norm_sq : Integrable (fun ω : Ω => ‖m.noise ω‖ ^ 2) ℙ := by
        simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
        exact integrable_finset_sum _ (fun i _ => h_int_sq i)
      obtain ⟨f, hf_meas, hf_eq⟩ := h_int_norm_sq.aemeasurable
      have hm1 : ℙ {ω | ‖m.noise ω‖ ^ 2 < threshold} = ℙ {ω | f ω < threshold} :=
        measure_congr (hf_eq.mono (fun _ h => congr_arg (· < threshold) h))
      have hm2 : ℙ {ω | ‖m.noise ω‖ ^ 2 ≥ threshold} = ℙ {ω | f ω ≥ threshold} :=
        measure_congr (hf_eq.mono (fun _ h => congr_arg (· ≥ threshold) h))
      rw [hm1, hm2]
      have h_disj : Disjoint {ω : Ω | f ω < threshold} {ω : Ω | f ω ≥ threshold} :=
        Set.disjoint_left.mpr (fun ω h1 h2 => by simp only [ge_iff_le, Set.mem_setOf_eq] at h1 h2; linarith)
      have ht : MeasurableSet {ω : Ω | f ω ≥ threshold} := measurableSet_le (measurable_const (a := threshold)) hf_meas
      rw [← measure_union h_disj ht]
      have h_univ : {ω | f ω < threshold} ∪ {ω | f ω ≥ threshold} = Set.univ := by
        ext ω; simp only [ge_iff_le, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact lt_or_ge (f ω) threshold
      rw [h_univ, measure_univ, ENNReal.toReal_one]
  linarith

end Probability

end LeanSharp
