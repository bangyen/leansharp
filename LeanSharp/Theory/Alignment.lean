/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Stochastic.Mechanics.DescentSteps.ZScore
import LeanSharp.Theory.Robustness.SensitivityBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Notation
import Mathlib.Tactic.Linarith

namespace LeanSharp

open Real InnerProductSpace ProbabilityTheory MeasureTheory BigOperators

/-!
# Alignment Theory

This module unifies the deterministic and stochastic alignment conditions used
in convergence proofs. By standardizing these contracts, we ensure that
theoretical analysis remains consistent across different dynamical regimes.

## Main definitions

* `AlignmentCondition`: Deterministic descent direction alignment.
* `StochasticAlignmentCondition`: Generalization for stochastic processes.
* `StabilityCertificate`: Bundles forward pass with regularity properties.

## Main theorems

* `inner_hadamard_comm`: Geometric identity for Hadamard products.
* `alignment_filtered_gradient`: Proof that Z-score filtering preserves alignment.
* `alignment_condition_of_signal_noise`: Bridge theorem for stochastic models.
-/

variable {ι : Type*} [Fintype ι]

/-- **Deterministic Alignment Condition**: A descent direction `g` is $(\mu, L)$-aligned
    relative to a target `w_star` if it has sufficient inner product and bounded norm. -/
def AlignmentCondition (w w_star : W ι) (g : W ι) (μ L_smooth : ℝ) : Prop :=
  μ * ‖w - w_star‖^2 ≤ @inner ℝ _ _ g (w - w_star) ∧
  ‖g‖ ≤ L_smooth * ‖w - w_star‖

universe u
variable {Ω : Type u} [MeasureSpace Ω]

/-- **Stochastic Alignment Condition**: A stochastic descent direction `g` is $(\mu, \eta)$-aligned
    relative to a target `w_star` if its net expected progress exceeds the target threshold. -/
def StochasticAlignmentCondition (w w_star : W ι) (g : Ω → W ι) (η μ : ℝ) (z : ℝ) : Prop :=
  let g_f (ω : Ω) := filteredGradient (g ω) z
  Integrable g_f ∧
  Integrable (fun ω => ‖g_f ω‖ ^ 2) ∧
  2 * η * (@inner ℝ _ _ (𝔼[g_f]) (w - w_star)) -
  η^2 * 𝔼[fun ω => ‖g_f ω‖ ^ 2] ≥ η * μ * ‖w - w_star‖ ^ 2

/-- **Stability Certificate**: Bundles a forward pass operation with its analytical
    regularity properties (Lipschitz continuity and differentiability).
    By enforcing `ContDiffOn ℝ 2`, this certificate ensures that the layer is
    compatible with Hessian-based second-order analysis within a stable region. -/
structure StabilityCertificate (α β : Type*) [NormedAddCommGroup α] [NormedSpace ℝ α]
  [NormedAddCommGroup β] [NormedSpace ℝ β] where
  /-- The forward pass mapping. -/
  f : α → β
  /-- Domain of stability. -/
  S : Set α
  /-- Lipschitz constant witness. -/
  K : NNReal
  /-- Proof of Lipschitz continuity on S. -/
  h_lipschitz : LipschitzOnWith K f S
  /-- Proof of $C^2$ smoothness on S. -/
  h_smooth : ContDiffOn ℝ 2 f S

/-- **Certificate Composition**: If two maps are stability-certified, their
    composition is also certified. The Lipschitz constant is the product
    of the individual constants. -/
noncomputable def StabilityCertificate.comp {α β γ : Type*}
    [NormedAddCommGroup α] [NormedSpace ℝ α]
    [NormedAddCommGroup β] [NormedSpace ℝ β]
    [NormedAddCommGroup γ] [NormedSpace ℝ γ]
    (c2 : StabilityCertificate β γ) (c1 : StabilityCertificate α β) :
    StabilityCertificate α γ where
  f := c2.f ∘ c1.f
  S := c1.S ∩ (c1.f ⁻¹' c2.S)
  K := c2.K * c1.K
  h_lipschitz := c2.h_lipschitz.comp (c1.h_lipschitz.mono Set.inter_subset_left) (by intro x hx; exact hx.2)
  h_smooth := ContDiffOn.comp c2.h_smooth (c1.h_smooth.mono Set.inter_subset_left) (by intro x hx; exact hx.2)

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
    (h_align : μ * ‖v‖ ^ 2 ≤ inner ℝ g v)
    (h_filter_safe : ∀ i, (WithLp.equiv 2 (ι → ℝ) (zScoreMask g z)) i = 0 →
      (WithLp.equiv 2 (ι → ℝ) v i) * (WithLp.equiv 2 (ι → ℝ) g i) ≤ 0) :
    μ * ‖v‖ ^ 2 ≤ inner ℝ (filteredGradient g z) v := by
  unfold filteredGradient
  rw [inner_hadamard_comm]
  apply h_align.trans
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Star.star, id_eq]
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
    (w w_star : W ι) (z μ L_smooth : ℝ) (ω : Ω) (m : SignalNoiseModel ι Ω)
    (h_align : μ * ‖w - w_star‖ ^ 2 ≤ inner ℝ (m.observed ω) (w - w_star))
    (h_norm : ‖filteredGradient (m.observed ω) z‖ ≤ L_smooth * ‖w - w_star‖)
    (h_safe : ∀ i, (WithLp.equiv 2 (ι → ℝ) (zScoreMask (m.observed ω) z)) i = 0 →
      (WithLp.equiv 2 (ι → ℝ) (w - w_star) i) * (WithLp.equiv 2 (ι → ℝ) (m.observed ω) i) ≤ 0) :
    AlignmentCondition w w_star (filteredGradient (m.observed ω) z) μ L_smooth := by
  constructor
  · exact alignment_filtered_gradient (m.observed ω) (w - w_star) μ z h_align h_safe
  · exact h_norm

end LeanSharp
