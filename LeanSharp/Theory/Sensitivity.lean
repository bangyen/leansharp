/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

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
  g_true : W ι
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
  dsimp [SignalNoiseModel.observed, vector_mean]
  have h_card : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp only [add_sub_cancel_left]
  rw [abs_div, abs_of_pos h_card]
  apply div_le_div_of_nonneg_right _ h_card.le
  exact Finset.abs_sum_le_sum_abs _ _

/-- Bounded variance assumption for the noise vector components. -/
def noise_variance_bound (m : SignalNoiseModel ι Ω) (σsq : ℝ) : Prop :=
  ∀ i : ι, 𝔼[fun ω => ((WithLp.equiv 2 (ι → ℝ) (m.noise ω)) i)^2] ≤ σsq

/-- The event that the $i$-th component is preserved by the Z-score filter. -/
def preservation_event (m : SignalNoiseModel ι Ω) (z : ℝ) (i : ι) : Set Ω :=
  {ω | |(WithLp.equiv 2 (ι → ℝ) (m.observed ω)) i - vector_mean (m.observed ω)| ≥
    z * vector_std (m.observed ω)}

section Probability
variable [IsProbabilityMeasure (volume : Measure Ω)]

/-- The probability of the preservation event. -/
noncomputable def preservation_prob (m : SignalNoiseModel ι Ω) (z : ℝ) (i : ι) : ℝ :=
  (ℙ (preservation_event m z i)).toReal

/-- **Mean Deviation Bound**: The expectation of the error in vector mean is zero. -/
lemma vector_mean_observed_expected (m : SignalNoiseModel ι Ω) [Nonempty ι] :
    𝔼[fun ω => vector_mean (m.observed ω)] = vector_mean m.g_true := by
  dsimp [SignalNoiseModel.observed, vector_mean]
  have h_card : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [MeasureTheory.integral_div]
  congr 1
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    have h_int_noise_i : Integrable (fun a => (m.noise a) i) :=
      (EuclideanSpace.proj i : (W ι) →L[ℝ] ℝ).integrable_comp m.h_int
    rw [MeasureTheory.integral_add (integrable_const _) h_int_noise_i]
    have h_zero : ∫ (a : Ω), (m.noise a) i = 0 := by
      change ∫ (a : Ω), (EuclideanSpace.proj i : W ι →L[ℝ] ℝ) (m.noise a) = 0
      rw [ContinuousLinearMap.integral_comp_comm, m.h_mean]
      · simp only [ContinuousLinearMap.map_zero]
      · exact m.h_int
    simp only [integral_const, probReal_univ, one_smul, h_zero, add_zero]
  · intro i _; exact (integrable_const _).add
      ((EuclideanSpace.proj i : (W ι) →L[ℝ] ℝ).integrable_comp m.h_int)

/-- **Z-Score Sensitivity Bound (Informal)**:
If the true gradient signal is significantly above the noise-deviated Z-score,
the component is preserved. -/
theorem preservation_prob_lower_bound (m : SignalNoiseModel ι Ω) (z : ℝ) (i : ι)
    (h_sig : |(WithLp.equiv 2 _ m.g_true) i - vector_mean m.g_true| ≥ z * vector_std m.g_true + 1)
    (σ_sq : ℝ) (h_noise : noise_variance_bound m σ_sq) :
    preservation_prob m z i ≥ 1 - (σ_sq * (Fintype.card ι : ℝ).sqrt) := by
  sorry -- Full proof requires concentration of empirical covariance.

end Probability

end LeanSharp
