/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Stats
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Filtered Mean Robustness

This module exists to isolate filtered empirical-mean definitions and bounds so
other robustness proofs can depend on a compact, reusable mean-aggregation API.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι]
variable {α : Type*}

open BigOperators

/-- A constant unit vector in $W$. -/
noncomputable def unit_vector (ι : Type*) [Fintype ι] : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm fun _ => 1 / Real.sqrt (Fintype.card ι)

lemma norm_unit_vector (ι : Type*) [Fintype ι] [Nonempty ι] : ‖unit_vector ι‖ = 1 := by
  unfold unit_vector
  rw [EuclideanSpace.norm_eq]
  simp only [WithLp.equiv_symm_apply, Real.norm_eq_abs, sq_abs]
  have card_pos : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_sq : (1 / Real.sqrt (Fintype.card ι))^2 = 1 / (Fintype.card ι : ℝ) := by
    rw [one_div, inv_pow, Real.sq_sqrt card_pos]; field_simp
  simp only [h_sq]
  have card_ne_zero : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := ι))
  rw [mul_one_div_cancel card_ne_zero, Real.sqrt_one]

/-- The empirical mean of a collection of vectors. -/
noncomputable def empirical_mean (s : Finset α) (g : α → W ι) : W ι :=
  (1 / (s.card : ℝ)) • ∑ i ∈ s, g i

/-- The empirical mean after applying coordinate-wise Z-score filtering to each vector.
This estimator starts the bridge between classical outlier robustness and Z-score gating. -/
noncomputable def z_filtered_empirical_mean (s : Finset α) (g : α → W ι) (z : ℝ) : W ι :=
  empirical_mean s (fun i => filtered_gradient (g i) z)

/-- **Filtered mean norm control**: the norm of the Z-filtered empirical mean is bounded
by the average unfiltered norm over the sample. This gives a direct quantitative handle
for robust bounds that combine filtering with aggregation. -/
theorem z_filtered_empirical_mean_norm_le
    (s : Finset α) (g : α → W ι) (z : ℝ) (hs : s.Nonempty) :
    ‖z_filtered_empirical_mean s g z‖ ≤ (1 / (s.card : ℝ)) * (∑ i ∈ s, ‖g i‖) := by
  unfold z_filtered_empirical_mean empirical_mean
  have hn_pos : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn_pos)]
  calc
    (1 / (s.card : ℝ)) * ‖∑ i ∈ s, filtered_gradient (g i) z‖
      ≤ (1 / (s.card : ℝ)) * (∑ i ∈ s, ‖filtered_gradient (g i) z‖) := by
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (1 / (s.card : ℝ)) * (∑ i ∈ s, ‖g i‖) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum (fun i _ => filtered_norm_bound (g i) z)
        · positivity

/-- **Uniform-input bound for filtered mean**: if every sample gradient has norm at most
`R`, then the Z-filtered empirical mean also has norm at most `R`. This is the first
reusable step toward deciding when filtered-mean aggregation is safe. -/
theorem z_filtered_empirical_mean_norm_le_of_pointwise_bound
    (s : Finset α) (g : α → W ι) (z R : ℝ) (hs : s.Nonempty)
    (hR : ∀ i ∈ s, ‖g i‖ ≤ R) :
    ‖z_filtered_empirical_mean s g z‖ ≤ R := by
  have h_base := z_filtered_empirical_mean_norm_le s g z hs
  have hn_pos : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  refine h_base.trans ?_
  calc
    (1 / (s.card : ℝ)) * (∑ i ∈ s, ‖g i‖)
      ≤ (1 / (s.card : ℝ)) * (∑ i ∈ s, R) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum (fun i hi => hR i hi)
        · positivity
    _ = (1 / (s.card : ℝ)) * ((s.card : ℝ) * R) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = R := by
        field_simp [ne_of_gt hn_pos]

/-- **Subset-robust filtered-mean bound**: if indices in `s_fixed` are unchanged and bounded
by `R_fixed`, while changed indices in `s \ s_fixed` are bounded by `R_out`, then the
Z-filtered empirical mean is bounded by the corresponding weighted average radius. -/
theorem z_filtered_empirical_mean_bounded_subset
    [DecidableEq α]
    (s : Finset α) (g : α → W ι) (s_fixed : Finset α) (h_sub : s_fixed ⊆ s)
    (z R_fixed R_out : ℝ) (hs : s.Nonempty)
    (h_fixed_bound : ∀ i ∈ s_fixed, ‖g i‖ ≤ R_fixed) :
    ∀ g' : α → W ι, (∀ i ∈ s_fixed, g' i = g i) →
      (∀ i ∈ s \ s_fixed, ‖g' i‖ ≤ R_out) →
      ‖z_filtered_empirical_mean s g' z‖ ≤
        (1 / (s.card : ℝ)) *
          (((s_fixed.card : ℝ) * R_fixed) + (((s \ s_fixed).card : ℝ) * R_out)) := by
  intro g' hg_fixed hg_out
  let s_out := s \ s_fixed
  have h_base := z_filtered_empirical_mean_norm_le s g' z hs
  have h_sum_split_raw :
      ∑ i ∈ s, ‖g' i‖ = (∑ i ∈ s_fixed, ‖g' i‖) + (∑ i ∈ s \ s_fixed, ‖g' i‖) := by
    have h_filter_eq : s.filter (fun i => i ∈ s_fixed) = s_fixed := by
      ext i
      constructor
      · intro hi
        exact (Finset.mem_filter.mp hi).2
      · intro hi
        exact Finset.mem_filter.mpr ⟨h_sub hi, hi⟩
    have h_filter_not_eq : s.filter (fun i => i ∉ s_fixed) = s \ s_fixed := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_sdiff]
    simpa only [Finset.sum_filter, h_filter_eq, h_filter_not_eq] using
      (Finset.sum_filter_add_sum_filter_not
        (s := s) (f := fun i => ‖g' i‖) (p := fun i => i ∈ s_fixed)).symm
  have h_sum_split : ∑ i ∈ s, ‖g' i‖ = (∑ i ∈ s_fixed, ‖g' i‖) + (∑ i ∈ s_out, ‖g' i‖) := by
    simpa only [s_out] using h_sum_split_raw
  have h_fixed_sum : (∑ i ∈ s_fixed, ‖g' i‖) ≤ ∑ i ∈ s_fixed, R_fixed := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    calc ‖g' i‖ = ‖g i‖ := by rw [hg_fixed i hi]
      _ ≤ R_fixed := h_fixed_bound i hi
  have h_out_sum : (∑ i ∈ s_out, ‖g' i‖) ≤ ∑ i ∈ s_out, R_out := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    exact hg_out i (by simpa only [s_out] using hi)
  have h_sum_bound : (1 / (s.card : ℝ)) * (∑ i ∈ s, ‖g' i‖)
      ≤ (1 / (s.card : ℝ)) * ((∑ i ∈ s_fixed, R_fixed) + (∑ i ∈ s_out, R_out)) := by
    apply mul_le_mul_of_nonneg_left
    · rw [h_sum_split]
      exact add_le_add h_fixed_sum h_out_sum
    · positivity
  have h_sum_bound' : (1 / (s.card : ℝ)) * (∑ i ∈ s, ‖g' i‖)
      ≤ (1 / (s.card : ℝ)) *
          (((s_fixed.card : ℝ) * R_fixed) + (((s \ s_fixed).card : ℝ) * R_out)) := by
    calc
      (1 / (s.card : ℝ)) * (∑ i ∈ s, ‖g' i‖)
        ≤ (1 / (s.card : ℝ)) * ((∑ i ∈ s_fixed, R_fixed) + (∑ i ∈ s_out, R_out)) := h_sum_bound
      _ = (1 / (s.card : ℝ)) * (((s_fixed.card : ℝ) * R_fixed) + ((s_out.card : ℝ) * R_out)) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul]
      _ = (1 / (s.card : ℝ)) *
            (((s_fixed.card : ℝ) * R_fixed) + (((s \ s_fixed).card : ℝ) * R_out)) := by
            simp only [one_div, s_out]
  exact h_base.trans h_sum_bound'

end LeanSharp
