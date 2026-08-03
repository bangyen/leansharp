/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.StatsBounds
import LeanSharp.Theory.Concentration
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.Basic

/-!
# Infinite-Width Analytical Limits

This module provides the formal foundation for analyzing the generalization
and structural properties of neural networks in the infinite-width limit ($D \to \infty$).

As LeanSharp defines parameter dimensions via finite types (`Fintype ι`), taking
the limit requires a sequence of topological index sets where the cardinality
diverges to infinity, while functional metrics (mean, variance) converge
to their analytical distributions.

## Main Definitions

* `DimensionSequence`: A sequence of finite index types.
* `IsInfiniteWidth`: A property asserting that the parameter count diverges to `atTop`.
* `HasAnalyticalMean`: Defines the topological limit of empirical sums.
* `HasAnalyticalStd`: Defines the topological limit of empirical standard deviation.
* `HasAnalyticalFilteredMean`: Defines topological limit of the Z-score filtered empirical mean.
* `HasAnalyticalFilteredStd`: Defines topological limit of the Z-score filtered standard deviation.

## Theorems

* `std_analytical_nonneg`: Proves that topological limit scaling preserves standard
  deviation non-negativity natively bridging discrete constraints to infinite domains.
* `ConcentrationStabilityTheorem`: Proves infinite-width Z-score mask coverage via Chebyshev.
* `filteredNormDominated`: Proves the filtered gradient norms are eventually bounded above
  in the infinite-width limit whenever the unfiltered norms converge.
* `filteredMeanDominated`: Proves the filtered mean is eventually bounded in the limit.
* `filteredStdDominated`: Proves the filtered standard deviation is eventually bounded
  in the limit.
-/

namespace LeanSharp

open Filter Topology Real

/-- A sequence of parameter index spaces, indexed by $n \in \mathbb{N}$. -/
structure DimensionSequence where
  /-- The sequence of dimension types representing finite layer widths. -/
  ι : ℕ → Type
  /-- Each topological width slice must be fully finite to permit empirical SAM filtering. -/
  fintype_ι : ∀ n, Fintype (ι n)

namespace DimensionSequence

/-- To analyze the infinite width limit natively, the dimensionality of the sequence
    must strictly diverge to positive infinity. -/
class IsInfiniteWidth (D : DimensionSequence) : Prop where
  /-- The sequence of layer dimensions $D_n \to \infty$. -/
  card_tendsto_atTop : Tendsto (fun n => @Fintype.card (D.ι n) (D.fintype_ι n)) atTop atTop

instance instFintype {D : DimensionSequence} {n : ℕ} : Fintype (D.ι n) := D.fintype_ι n

/-- A sequence of gradient evaluations along the width scaling dimension. -/
abbrev GradientSequence (D : DimensionSequence) := ∀ n, W (D.ι n)

/-- Formally defines the existence of a macroscopic analytical mean as width approaches infinity.
    This replaces discrete empirical bounds with a topological limit over networks. -/
def HasAnalyticalMean (D : DimensionSequence) (g : GradientSequence D) (μ : ℝ) : Prop :=
  Tendsto (fun n => @vectorMean (D.ι n) (D.fintype_ι n) (g n)) atTop (nhds μ)

/-- Formally defines the macroscopic analytical variance/std limit.
    Crucial for analyzing the Z-score SAM bounds in NTK regimes. -/
def HasAnalyticalStd (D : DimensionSequence) (g : GradientSequence D) (σ : ℝ) : Prop :=
  Tendsto (fun n => @vectorStd (D.ι n) (D.fintype_ι n) (g n)) atTop (nhds σ)

/-- Analytical consistency requires standard deviations to be non-negative in the limit. -/
lemma std_analytical_nonneg {D : DimensionSequence} {g : GradientSequence D} {σ : ℝ}
    (h : HasAnalyticalStd D g σ) : 0 ≤ σ := by
  apply ge_of_tendsto h
  filter_upwards []
  intro n
  unfold vectorStd
  exact Real.sqrt_nonneg _

/-- Sequence of Z-score filtered gradients. -/
noncomputable def FilteredSequence
    (D : DimensionSequence) (g : GradientSequence D) (z : ℝ) : GradientSequence D :=
  fun n => filteredGradient (g n) z

/-- Formally defines the limit of the empirical mean of a filtered gradient sequence. -/
def HasAnalyticalFilteredMean (D : DimensionSequence) (g : GradientSequence D) (z μ_f : ℝ) : Prop :=
  HasAnalyticalMean D (FilteredSequence D g z) μ_f

/-- Formally defines the limit of the empirical standard deviation of a filtered gradient sequence.
-/
def HasAnalyticalFilteredStd (D : DimensionSequence) (g : GradientSequence D) (z σ_f : ℝ) : Prop :=
  HasAnalyticalStd D (FilteredSequence D g z) σ_f

/-- **Concentration Stability Theorem**:
If dimension diverges, the empirical Z-score mask's coverage is upper-bounded by $1/z^2$
due to discrete vector concentration (Chebyshev). This bridges the geometry of finite-width
networks with stable analytical generalization limits. -/
theorem ConcentrationStabilityTheorem (D : DimensionSequence)
    (g : GradientSequence D) (z : ℝ) (hz : 0 < z)
    (h_var_pos : ∀ n, vectorVariance (g n) > 0)
    (h_nonempty : ∀ n, Nonempty (D.ι n)) :
    Tendsto (fun n =>
      letI : Nonempty (D.ι n) := h_nonempty n
      ((LeanSharp.zScoreTails (g n) z).card : ℝ) / (@Fintype.card (D.ι n) (D.fintype_ι n) : ℝ))
      atTop (principal (Set.Iic (1 / z^2 : ℝ))) := by
  rw [tendsto_principal]
  filter_upwards [] with n
  letI : Nonempty (D.ι n) := h_nonempty n
  exact chebyshev_vector (g n) hz (h_var_pos n)

/-- **Filtered Norm Domination**: In the infinite-width limit, if the unfiltered gradient
norms converge to `c`, then the Z-score filtered gradient norms are eventually bounded above
by `c + ε` for any `ε > 0`. This is the asymptotic counterpart of `norm_filtered_gradient_le`:
the filter never amplifies the gradient, so it cannot create growth in the limit. -/
theorem filteredNormDominated {D : DimensionSequence} {g : GradientSequence D} {z c : ℝ}
    (h : Tendsto (fun n => ‖g n‖) atTop (nhds c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ‖FilteredSequence D g z n‖ ≤ c + ε := by
  intro ε hε
  have hg : ∀ᶠ n in atTop, ‖g n‖ < c + ε :=
    h.eventually (IsOpen.mem_nhds isOpen_Iio (lt_add_of_pos_right c hε))
  filter_upwards [hg] with n hn
  calc
    ‖FilteredSequence D g z n‖ = ‖filteredGradient (g n) z‖ := rfl
    _ ≤ ‖g n‖ := norm_filtered_gradient_le (g n) z
    _ ≤ c + ε := le_of_lt hn

/-- **Filtered Mean Domination**: In the infinite-width limit, if the unfiltered gradient
norms converge to `c`, then the empirical mean of the Z-score filtered gradient is
eventually bounded above by `c + ε`. This is the infinite-width counterpart of
`abs_vectorMean_le_norm`: the mean never exceeds the norm, so it inherits the norm's
asymptotic boundedness. -/
theorem filteredMeanDominated {D : DimensionSequence} {g : GradientSequence D} {z c : ℝ}
    (h : Tendsto (fun n => ‖g n‖) atTop (nhds c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      |vectorMean (FilteredSequence D g z n)| ≤ c + ε := by
  intro ε hε
  have hnrm := filteredNormDominated (D := D) (g := g) (z := z) h ε hε
  filter_upwards [hnrm] with n hn
  calc
    |vectorMean (FilteredSequence D g z n)| ≤ ‖FilteredSequence D g z n‖ :=
      abs_vectorMean_le_norm _
    _ ≤ c + ε := hn

/-- **Filtered Std Domination**: In the infinite-width limit, if the unfiltered gradient
norms converge to `c`, then the empirical standard deviation of the Z-score filtered
gradient is eventually bounded above by `c + ε`. This is the infinite-width counterpart of
`vectorStd_le_norm`. -/
theorem filteredStdDominated {D : DimensionSequence} {g : GradientSequence D} {z c : ℝ}
    (h : Tendsto (fun n => ‖g n‖) atTop (nhds c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      vectorStd (FilteredSequence D g z n) ≤ c + ε := by
  intro ε hε
  have hnrm := filteredNormDominated (D := D) (g := g) (z := z) h ε hε
  filter_upwards [hnrm] with n hn
  calc
    vectorStd (FilteredSequence D g z n) ≤ ‖FilteredSequence D g z n‖ :=
      vectorStd_le_norm _
    _ ≤ c + ε := hn

end DimensionSequence

end LeanSharp
