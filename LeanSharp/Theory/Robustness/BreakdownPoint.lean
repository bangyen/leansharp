/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.MedianComparison
import Mathlib.Tactic.Linarith

/-!
# Breakdown Point Theory

This module exists to formalize finite-sample breakdown-point definitions and
to prove baseline lower/upper bounds for mean and geometric-median estimators.

## Definitions

* `IsBoundedAtOutlierCount`.
* `finiteSampleBreakdownPoint`.

## Theorems

* `mean_breakdown_point_zero`.
* `geometric_median_breakdown_point_ge_half`.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι]
variable {α : Type*}

open BigOperators

/-- An estimator is bounded at outlier count `k` if the estimate remains in a bounded set
whenever at most `k` points are moved from the original dataset `g`. -/
def IsBoundedAtOutlierCount (s : Finset α) (g : α → W ι)
    (k : ℕ) (est : (α → W ι) → W ι) : Prop :=
  ∃ R : ℝ, ∀ g' : α → W ι, (s.filter (fun i => g' i ≠ g i)).card ≤ k →
    ‖est g'‖ ≤ R

/-- The finite-sample breakdown point is the smallest fraction $k/n$ of outliers
that can move the estimate arbitrarily far. -/
noncomputable def finiteSampleBreakdownPoint (s : Finset α) (g : α → W ι)
    (est : (α → W ι) → W ι) : ℝ := by
  classical
  exact if h : ∃ k : ℕ, ¬ IsBoundedAtOutlierCount s g k est then
    (Nat.find h : ℕ) / (s.card : ℝ)
  else
    1

/-- **Mean Breakdown Point is Zero**: Moving a single point can break the empirical mean. -/
theorem mean_breakdown_point_zero [Nonempty ι] (s : Finset α) (g : α → W ι)
    (hs : s.Nonempty) :
    finiteSampleBreakdownPoint s g (empiricalMean s) ≤ 1 / (s.card : ℝ) := by
  classical
  unfold finiteSampleBreakdownPoint
  have h_one : ¬ IsBoundedAtOutlierCount s g 1 (empiricalMean s) := by
    unfold IsBoundedAtOutlierCount
    push_neg
    intro R
    let i0 := hs.choose
    have hi0 : i0 ∈ s := hs.choose_spec
    let C := max R 0 + 1
    obtain ⟨g', h_diff, h_norm⟩ := mean_unbounded s g i0 hi0 C
    refine ⟨g', ?_, ?_⟩
    · have hsub : s.filter (fun i => g' i ≠ g i) ⊆ ({i0} : Finset α) := by
        intro i hi
        simp only [Finset.mem_singleton]
        simp only [Finset.mem_filter] at hi
        by_contra hneq
        exact hi.2 (h_diff i hneq)
      exact le_trans (Finset.card_le_card hsub)
        (by simp only [Finset.card_singleton, le_refl])
    · have hRC : R < C := by
        unfold C
        linarith [le_max_left R 0]
      exact lt_trans hRC h_norm
  let h_exists : ∃ k : ℕ, ¬ IsBoundedAtOutlierCount s g k (empiricalMean s) := ⟨1, h_one⟩
  rw [dif_pos h_exists]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.find_min' h_exists h_one
  · positivity

/-- **Geometric Median Breakdown point is at least Half**. -/
theorem geometric_median_breakdown_point_ge_half
    (s : Finset α) (g : α → W ι) (hs : s.Nonempty) :
    finiteSampleBreakdownPoint s g (geometricMedian s) ≥ 1 / 2 := by
  classical
  unfold finiteSampleBreakdownPoint
  by_cases h_non : ∃ k : ℕ, ¬ IsBoundedAtOutlierCount s g k (geometricMedian s)
  · rw [dif_pos h_non]
    let k0 := Nat.find h_non
    have hk0_not_bounded : ¬ IsBoundedAtOutlierCount s g k0 (geometricMedian s) :=
      Nat.find_spec h_non
    have h_bounded_lt_half :
        ∀ k : ℕ, 2 * k < s.card → IsBoundedAtOutlierCount s g k (geometricMedian s) := by
      intro k hk
      unfold IsBoundedAtOutlierCount
      let B : Finset α → ℝ := fun sf =>
        if hsf : sf ⊆ s ∧ 2 * sf.card > s.card then
          |Classical.choose (median_bounded_subset s g sf hsf.1 hsf.2)|
        else
          0
      use ∑ sf ∈ s.powerset, B sf
      intro g' hg'
      let sf := s.filter (fun i => g' i = g i)
      have hsf_sub : sf ⊆ s := Finset.filter_subset _ _
      have hsf_maj : 2 * sf.card > s.card := by
        have hsplit : sf.card + (s.filter (fun i => g' i ≠ g i)).card = s.card := by
          rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not s s _)]
          congr
          ext i
          constructor
          · intro hmem
            have hmem' : i ∈ s ∧ g' i = g i ∨ i ∈ s ∧ ¬ g' i = g i := by
              simpa only [sf, Finset.mem_union, Finset.mem_filter] using hmem
            rcases hmem' with hleft | hright
            · exact hleft.1
            · exact hright.1
          · intro his
            by_cases hEq : g' i = g i
            · have hmem' : i ∈ s ∧ g' i = g i ∨ i ∈ s ∧ ¬ g' i = g i := Or.inl ⟨his, hEq⟩
              simpa only [sf, Finset.mem_union, Finset.mem_filter] using hmem'
            · have hmem' : i ∈ s ∧ g' i = g i ∨ i ∈ s ∧ ¬ g' i = g i := Or.inr ⟨his, hEq⟩
              simpa only [sf, Finset.mem_union, Finset.mem_filter] using hmem'
        omega
      let R_sf := Classical.choose (median_bounded_subset s g sf hsf_sub hsf_maj)
      have h_med_le : ‖geometricMedian s g'‖ ≤ R_sf := by
        have H := Classical.choose_spec (median_bounded_subset s g sf hsf_sub hsf_maj)
        apply H g'
        intro i hi
        have hi' : i ∈ s ∧ g' i = g i := by
          simpa only [sf, Finset.mem_filter] using hi
        exact hi'.2
      have h_Rsf_le_abs : R_sf ≤ |R_sf| := le_abs_self R_sf
      have h_abs_eq_B : |R_sf| = B sf := by
        simp only [
          gt_iff_lt,
          hsf_sub,
          hsf_maj,
          and_self,
          ↓reduceDIte,
          R_sf, B
        ]
      have h_B_le_sum : B sf ≤ ∑ t ∈ s.powerset, B t := by
        apply Finset.single_le_sum
        · intro t ht
          by_cases hts : t ⊆ s ∧ 2 * t.card > s.card
          · simp only [gt_iff_lt, hts, and_self, ↓reduceDIte, abs_nonneg, B]
          · simp only [gt_iff_lt, hts, ↓reduceDIte, le_refl, B]
        · exact Finset.mem_powerset.2 hsf_sub
      have h_abs_le_sum : |R_sf| ≤ ∑ t ∈ s.powerset, B t := by
        simpa only [h_abs_eq_B] using h_B_le_sum
      exact h_med_le.trans (h_Rsf_le_abs.trans h_abs_le_sum)
    have hk0_ge_half_nat : s.card ≤ 2 * k0 := by
      by_contra hk0_ge
      have hk0_lt : 2 * k0 < s.card := by
        exact lt_of_not_ge hk0_ge
      exact hk0_not_bounded (h_bounded_lt_half k0 hk0_lt)
    have hs_card_pos : (0 : ℝ) < s.card := by
      exact_mod_cast hs.card_pos
    have hk0_ge_half_real : (s.card : ℝ) ≤ 2 * (k0 : ℝ) := by
      exact_mod_cast hk0_ge_half_nat
    rw [ge_iff_le]
    apply (le_div_iff₀ hs_card_pos).2
    nlinarith [hk0_ge_half_real]
  · rw [dif_neg h_non]
    norm_num

end LeanSharp
