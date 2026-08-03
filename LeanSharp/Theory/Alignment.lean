/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Stochastic.Mechanics.DescentSteps.ZScore
import LeanSharp.Theory.Robustness.SensitivityBounds
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Basic

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
* `deterministic_implies_stochastic_alignment`: Deterministic alignment implies
  the stochastic variant under a degenerate distribution.
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
  h_lipschitz := c2.h_lipschitz.comp
    (c1.h_lipschitz.mono Set.inter_subset_left) (by intro x hx; exact hx.2)
  h_smooth := ContDiffOn.comp c2.h_smooth
    (c1.h_smooth.mono Set.inter_subset_left) (by intro x hx; exact hx.2)

/-- **Locally-Lipschitz from $C^2$**: Any globally $C^2$ function between finite
dimensional Euclidean spaces is Lipschitz on every centered ball $B(0, R)$, with
Lipschitz constant the maximum Fréchet-derivative norm on the closed ball
(obtained via the Extreme Value Theorem). This factors out the shared boilerplate
of the layer Lipschitz proofs. -/
theorem lipschitzOnWith_closedBall_of_contDiff_two {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (R : ℝ) (hR : 0 < R)
    (h_c2 : ContDiff ℝ 2 f) :
    ∃ K, LipschitzOnWith K f (Metric.ball 0 R) := by
  have h_diff : ∀ x, DifferentiableAt ℝ f x := fun x => h_c2.differentiable (by decide) x
  have h_cont_deriv : Continuous (fderiv ℝ f) := h_c2.continuous_fderiv (by decide)
  have h_compact : IsCompact (Metric.closedBall (0 : E) R) :=
    isCompact_closedBall (0 : E) R
  have h_cont_norm : Continuous (fun x => ‖fderiv ℝ f x‖) :=
    continuous_norm.comp h_cont_deriv
  have h_nonempty : (Metric.closedBall (0 : E) R).Nonempty :=
    Metric.nonempty_closedBall.mpr hR.le
  obtain ⟨x0, _, h_max⟩ := IsCompact.exists_isMaxOn h_compact h_nonempty h_cont_norm.continuousOn
  let K := ‖fderiv ℝ f x0‖₊
  use K
  have h_lips : LipschitzOnWith K f (Metric.closedBall 0 R) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact fun x _ => h_diff x
    · exact fun x hx => h_max hx
    · exact convex_closedBall 0 R
  exact h_lips.mono Metric.ball_subset_closedBall

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

/-- **Alignment Bridging Theorem**: A mathematically formal bridge showing that
any deterministic gradient satisfying the deterministic AlignmentCondition also
satisfies the StochasticAlignmentCondition relative to a degenerate volume distribution,
provided the step-size respects the theoretical local "tightness" threshold bounding
smoothness against strong convexity. -/
theorem deterministic_implies_stochastic_alignment (Ω : Type*) [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (L : W ι → ℝ) (w w_star : W ι) (ε : W ι)
    (z μ L_smooth : ℝ) (η : ℕ → ℝ) (t : ℕ)
    (h_align : AlignmentCondition w w_star (filteredGradient (gradient L (w + ε)) z) μ L_smooth)
    (h_tight : η t * L_smooth ^ 2 ≤ μ) (h_eta : 0 ≤ η t) :
    StochasticAlignmentCondition (Ω := Ω) w w_star (fun _ => gradient L (w + ε)) (η t) μ z := by
  unfold StochasticAlignmentCondition AlignmentCondition at *
  let g_f := filteredGradient (gradient L (w + ε)) z
  have h1 : Integrable (fun _ : Ω => g_f) := integrable_const _
  have h2 : Integrable (fun _ : Ω => ‖g_f‖ ^ 2) := integrable_const _
  refine ⟨h1, h2, ?_⟩
  rw [integral_const, probReal_univ, one_smul]
  rw [integral_const, probReal_univ, one_smul]
  have h_mu : μ * ‖w - w_star‖^2 ≤ inner (𝕜 := ℝ) g_f (w - w_star) := h_align.1
  have h_L : ‖g_f‖ ≤ L_smooth * ‖w - w_star‖ := h_align.2
  have h_L_sq : ‖g_f‖^2 ≤ L_smooth^2 * ‖w - w_star‖^2 := by
    nlinarith [h_L, norm_nonneg g_f, norm_nonneg (w - w_star)]
  have h_tight_w : (η t) * (η t * L_smooth^2 * ‖w - w_star‖^2) ≤ η t * (μ * ‖w - w_star‖^2) := by
    apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_right h_tight (sq_nonneg ‖w - w_star‖)
    · exact h_eta
  calc η t * μ * ‖w - w_star‖^2
    _ = 2 * η t * (μ * ‖w - w_star‖^2) - η t * (μ * ‖w - w_star‖^2) := by ring
    _ ≤ 2 * η t * inner (𝕜 := ℝ) g_f (w - w_star) - η t * (μ * ‖w - w_star‖^2) := by
      apply sub_le_sub_right
      apply mul_le_mul_of_nonneg_left h_mu
      nlinarith [h_eta]
    _ ≤ 2 * η t * inner (𝕜 := ℝ) g_f (w - w_star) -
        (η t) * (η t * L_smooth^2 * ‖w - w_star‖^2) := by
      apply sub_le_sub_left h_tight_w
    _ = 2 * η t * inner (𝕜 := ℝ) g_f (w - w_star) -
        (η t)^2 * (L_smooth^2 * ‖w - w_star‖^2) := by ring
    _ ≤ 2 * η t * inner (𝕜 := ℝ) g_f (w - w_star) - (η t)^2 * ‖g_f‖^2 := by
      apply sub_le_sub_left
      apply mul_le_mul_of_nonneg_left h_L_sq
      nlinarith [sq_nonneg (η t)]

end LeanSharp
