/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Theory.Robustness.FilteredMeanProps.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.HasLaw

/-!
# Z-Score Filter Bias

This module proves the filter's core statistical guarantee: filtering noise drawn
from a symmetric law introduces no bias. Because the mask is even (sign-invariant —
it depends only on `|gᵢ − mean g|` and the standard deviation, both unchanged by
negation), the filtered gradient is an odd function of its input, and the expectation
of an odd function under a symmetric measure is zero. This holds for any symmetric
law, in particular the symmetric heavy-tailed (Cauchy, α-stable) noises that motivate
the Z-Score filter.

## Main Theorems

* `integral_odd_eq_zero_of_symmetric`: the expectation of an odd function under a
  sign-invariant measure is zero.
* `zScoreMask_neg`: the mask is even (sign-invariant).
* `filteredGradient_neg`: the filtered gradient is odd.
* `filtered_noise_mean_zero`: filtering symmetric noise is unbiased (`E[filteredGradient η z] = 0`).
* `zFilteredEmpiricalMean_symmetric_noise_mean_zero`: the filtered empirical mean of an
  i.i.d. sample from a symmetric law has zero expectation.
-/

namespace LeanSharp

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

noncomputable section

/-- **Odd function under a symmetric measure**: if `μ` is invariant under negation
and `f` is odd, then `∫ f dμ = 0`. -/
lemma integral_odd_eq_zero_of_symmetric
    {α : Type*} [MeasurableSpace α] [NormedAddCommGroup α] [BorelSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (h_sym : μ.map (fun x => -x) = μ)
    {f : α → E} (hf_int : Integrable f μ) (h_odd : ∀ x, f (-x) = -f x) :
    (∫ x, f x ∂μ) = 0 := by
  have h_map : (∫ x, f x ∂(μ.map (fun x : α => -x))) = ∫ x, f (-x) ∂μ :=
    integral_map (by fun_prop : AEMeasurable (fun x : α => -x) μ)
      (by simpa only [h_sym] using hf_int.aestronglyMeasurable)
  have h_swap : (∫ x, f x ∂μ) = ∫ x, f (-x) ∂μ := by
    conv_lhs => rw [← h_sym]
    exact h_map
  have h_odd_int : (∫ x, f (-x) ∂μ) = -∫ x, f x ∂μ := by
    calc
      (∫ x, f (-x) ∂μ) = ∫ x, -f x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall h_odd
      _ = -∫ x, f x ∂μ := by rw [integral_neg]
  have h : (∫ x, f x ∂μ) = -(∫ x, f x ∂μ) := by
    conv_lhs => rw [h_swap]
    rw [h_odd_int]
  have ha2 : (∫ x, f x ∂μ) + (∫ x, f x ∂μ) = 0 := by
    nth_rewrite 1 [h]
    rw [neg_add_cancel]
  have htwo : (2 : ℝ) • (∫ x, f x ∂μ) = 0 := by
    rw [two_smul]
    exact ha2
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : ℝ) ≠ 0)

/-- **The mask is even**: the Z-score mask is unchanged by negating the input, since
it depends only on `|gᵢ - mean g|` and the standard deviation. -/
lemma zScoreMask_neg (g : W ι) (z : ℝ) : zScoreMask (-g) z = zScoreMask g z := by
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext i
  unfold zScoreMask
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply]
  have hmean : vectorMean (-g) = -vectorMean g := by
    rw [← neg_one_smul (R := ℝ), vectorMean_smul, neg_one_mul]
  have hstd : vectorStd (-g) = vectorStd g := by
    rw [← neg_one_smul (R := ℝ), vectorStd_smul]
    norm_num
  rw [hmean, hstd]
  congr 1
  have hneg : (-g).ofLp i = -g.ofLp i := by rfl
  rw [hneg]
  rw [show -g.ofLp i - -vectorMean g = vectorMean g - g.ofLp i by ring]
  rw [abs_sub_comm]

/-- **The filtered gradient is odd**: filtering the negation of a gradient is the
negation of the filtered gradient. -/
lemma filteredGradient_neg (g : W ι) (z : ℝ) : filteredGradient (-g) z = -filteredGradient g z := by
  unfold filteredGradient hadamard
  rw [zScoreMask_neg]
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext i
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply]
  rw [show (-g).ofLp i = -g.ofLp i by rfl]
  rw [show (-(WithLp.equiv 2 (ι → ℝ)).symm (fun j => g.ofLp j * (zScoreMask g z).ofLp j)).ofLp i =
      -(g.ofLp i * (zScoreMask g z).ofLp i) by rfl]
  ring

/-- **Filter bias**: the Z-Score filter is unbiased on symmetric noise. For a law `D`
invariant under negation (e.g., symmetric Cauchy or α-stable), the expected filtered
gradient is zero: the filter removes outliers without injecting bias. -/
lemma filtered_noise_mean_zero (D : Measure (W ι)) (z : ℝ)
    (h_sym : D.map (fun g => -g) = D)
    (h_int : Integrable (fun g => filteredGradient g z) D) :
    (∫ g, filteredGradient g z ∂D) = 0 := by
  exact integral_odd_eq_zero_of_symmetric D h_sym h_int (fun g => filteredGradient_neg g z)

/-- **Filter bias on a sample**: the Z-Score filtered empirical mean of an i.i.d. sample
from a symmetric law has zero expectation. This is the unbiasedness guarantee for the
sample aggregation the algorithm actually uses. -/
lemma zFilteredEmpiricalMean_symmetric_noise_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {α : Type*} (s : Finset α) (η : α → Ω → W ι) (z : ℝ)
    (D : Measure (W ι)) (h_sym : D.map (fun g => -g) = D)
    (h_law : ∀ i ∈ s, HasLaw (η i) D P)
    (h_int : ∀ i ∈ s, Integrable (fun g => filteredGradient g z) D) :
    (∫ ω, zFilteredEmpiricalMean s (fun i => η i ω) z ∂P) = 0 := by
  have h_int_P : ∀ i ∈ s, Integrable (fun ω => filteredGradient (η i ω) z) P := by
    intro i hi
    have hg : Integrable (fun g => filteredGradient g z) (P.map (η i)) := by
      simpa only [(h_law i hi).map_eq] using h_int i hi
    exact hg.comp_aemeasurable (h_law i hi).aemeasurable
  calc
    (∫ ω, zFilteredEmpiricalMean s (fun i => η i ω) z ∂P)
        = (∫ ω, (1 / (s.card : ℝ)) • ∑ i ∈ s, filteredGradient (η i ω) z ∂P) := by
          rfl
    _ = (1 / (s.card : ℝ)) • ∑ i ∈ s, (∫ ω, filteredGradient (η i ω) z ∂P) := by
          rw [integral_smul]
          rw [integral_finset_sum s h_int_P]
    _ = (1 / (s.card : ℝ)) • ∑ i ∈ s, (∫ g, filteredGradient g z ∂D) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact HasLaw.integral_comp (h_law i hi) (h_int i hi).aestronglyMeasurable
    _ = (1 / (s.card : ℝ)) • ∑ i ∈ s, 0 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact filtered_noise_mean_zero D z h_sym (h_int i hi)
    _ = 0 := by
          simp only [Finset.sum_const_zero, smul_zero]

end

end LeanSharp
