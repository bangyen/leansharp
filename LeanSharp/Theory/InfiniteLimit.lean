/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

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

## Theorems

* `std_analytical_nonneg`: Proves that topological limit scaling preserves standard
  deviation non-negativity natively bridging discrete constraints to infinite domains.
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

end DimensionSequence

end LeanSharp
