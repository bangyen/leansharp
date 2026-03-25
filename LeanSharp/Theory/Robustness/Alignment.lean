/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Dynamics.Convergence
import LeanSharp.Theory.Robustness.SensitivityBounds
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Notation
import Mathlib.Tactic.Linarith

/-!
# Alignment Theory

This module formalizes the concept of gradient alignment and proves that
the Z-score filtering operation preserves sufficient descent alignment
for optimization convergence.

## Main definitions

* `IsAligned`: A predicate indicating that a gradient vector `g` is well-aligned
  with a target descent direction `v` (e.g., toward the optimum).
* `FilteredAlignmentCondition`: Lifts the alignment predicate to the filtered gradient.

## Main theorems

* `alignment_filtered_gradient`: Proves that the filtered gradient maintains
  alignment if the mask preserves the components that contribute most to the
  descent direction.
* `alignment_condition_of_signal_noise`: Proves that `AlignmentCondition` holds
  when a `SignalNoiseModel` satisfies the safety threshold.
-/

namespace LeanSharp

open Real InnerProductSpace BigOperators MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- A vector `g` is μ-aligned with direction `v` if their inner product
    is at least `μ * ‖v‖^2`. -/
def IsAligned (g v : W ι) (μ : ℝ) : Prop :=
  μ * ‖v‖^2 ≤ inner ℝ g v

/-- Alignment preservation under the Z-score filter for a specific threshold `z`. -/
def FilteredAlignmentCondition (g v : W ι) (μ z : ℝ) : Prop :=
  IsAligned (filteredGradient g z) v μ

/-- **Hadamard Inner Product Identity**:
    The inner product of a Hadamard product `hadamard a b` with `v` is the
    sum over components of `a_i * b_i * v_i`. -/
lemma inner_hadamard_comm (a b v : W ι) :
    inner ℝ (hadamard a b) v = ∑ i, (WithLp.equiv 2 (ι → ℝ) a i) * (WithLp.equiv 2 (ι → ℝ) b i)
      * (WithLp.equiv 2 (ι → ℝ) v i) := by
  let r := WithLp.equiv 2 (ι → ℝ)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Star.star, id_eq, WithLp.equiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  -- Projections for the components
  have h_a : a.ofLp i = r a i := rfl
  have h_b : b.ofLp i = r b i := rfl
  have h_v : v.ofLp i = r v i := rfl
  -- Dimensional equality handles the Hadamard expansion
  have h_had : (hadamard a b).ofLp i = r a i * r b i := rfl
  rw [h_had, h_v, h_a, h_b]
  ring

/-- **Filtered Alignment Preservation (Deterministic)**:
    If the Z-score filter only removes components that do not contribute
    positively to the alignment with `v`, then the filtered gradient
    preserves (or improves) the original alignment. -/
theorem alignment_filtered_gradient
    (g v : W ι) (μ z : ℝ)
    (h_align : IsAligned g v μ)
    (h_filter_safe : ∀ i, (WithLp.equiv 2 (ι → ℝ) (zScoreMask g z)) i = 0 →
      (WithLp.equiv 2 (ι → ℝ) v i) * (WithLp.equiv 2 (ι → ℝ) g i) ≤ 0) :
    FilteredAlignmentCondition g v μ z := by
  unfold FilteredAlignmentCondition IsAligned filteredGradient
  rw [inner_hadamard_comm]
  dsimp only [IsAligned] at h_align
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h_align
  simp only [dotProduct, Star.star, id_eq] at h_align
  apply h_align.trans
  apply Finset.sum_le_sum
  intro i _
  let r := WithLp.equiv 2 (ι → ℝ)
  -- Show mask value is 0 or 1
  have h_m_val : r (zScoreMask g z) i = 1 ∨ r (zScoreMask g z) i = 0 := by
    unfold zScoreMask
    erw [Equiv.apply_symm_apply]
    split_ifs
    · left; rfl
    · right; rfl
  by_cases h_m1 : r (zScoreMask g z) i = 1
  · rw [h_m1]
    have h_g : g.ofLp i = r g i := rfl
    have h_v : v.ofLp i = r v i := rfl
    rw [h_g, h_v]
    simp only [mul_one]
    linarith
  · have h0 : r (zScoreMask g z) i = 0 := by
      cases h_m_val
      · contradiction
      · assumption
    rw [h0]
    simp only [mul_zero, zero_mul]
    have h_g : g.ofLp i = r g i := rfl
    have h_v : v.ofLp i = r v i := rfl
    rw [h_g, h_v]
    exact h_filter_safe i h0

/-- **Stochastic Alignment Bridge**:
    If a signal-noise model's observation satisfies the safety condition
    (filtering only bad components), then the `AlignmentCondition` holds. -/
theorem alignment_condition_of_signal_noise (Ω : Type*) [MeasureSpace Ω]
    (L : W ι → ℝ) (w w_star : W ι) (ρ z μ L_smooth : ℝ) (ω : Ω) (m : SignalNoiseModel ι Ω)
    (h_obs : m.observed ω = gradient L (w + samPerturbation L w ρ))
    (h_align : IsAligned (m.observed ω) (w - w_star) μ)
    (h_norm : ‖filteredGradient (m.observed ω) z‖ ≤ L_smooth * ‖w - w_star‖)
    (h_safe : ∀ i, (WithLp.equiv 2 (ι → ℝ) (zScoreMask (m.observed ω) z)) i = 0 →
      (WithLp.equiv 2 (ι → ℝ) (w - w_star) i) * (WithLp.equiv 2 (ι → ℝ) (m.observed ω) i) ≤ 0) :
    AlignmentCondition L w w_star (samPerturbation L w ρ) z μ L_smooth := by
  unfold AlignmentCondition
  dsimp only
  constructor
  · rw [← h_obs]
    exact alignment_filtered_gradient (m.observed ω) (w - w_star) μ z h_align h_safe
  · rw [← h_obs]
    exact h_norm

end LeanSharp
