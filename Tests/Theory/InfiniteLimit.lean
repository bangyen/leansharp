/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.InfiniteLimit
import Mathlib.Data.Fintype.Basic

/-!
# Infinite Limit Tests

This module verifies that standard dimension sequences (like Fin(n)) correctly
satisfy the `IsInfiniteWidth` property.

 ## Main Definitions

 * `standardDimSequence`: A concrete width sequence.

 ## Theorems

 * `test_is_infinite_width_standard`: Divergence proof.
 -/

namespace LeanSharp.Tests

open Filter DimensionSequence

/-- **Standard Dimension Sequence**:
ι_n = Fin(n).
The cardinality of ι_n is exactly n. -/
def standardDimSequence : DimensionSequence where
  ι n := Fin n
  fintype_ι _ := inferInstance

/-- **Infinite Width verification**:
Verifies that the standard Fin(n) sequence is indeed `IsInfiniteWidth`,
meaning its cardinality tends to infinity. -/
instance : IsInfiniteWidth standardDimSequence where
  card_tendsto_atTop := by
    simp only [standardDimSequence, Fintype.card_fin]
    exact tendsto_id

/-- **Filtered Norm Domination wiring**: With a convergent unfiltered gradient norm,
the filtered sequence is eventually bounded above by the limit plus epsilon. -/
example (D : DimensionSequence) (g : D.GradientSequence) (z c : ℝ)
    (h : Tendsto (fun n => ‖g n‖) atTop (nhds c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ‖FilteredSequence D g z n‖ ≤ c + ε :=
  filteredNormDominated h

/-- **Filtered Mean Domination wiring**: the filtered mean is eventually bounded in the
infinite-width limit. -/
example (D : DimensionSequence) (g : D.GradientSequence) (z c : ℝ)
    (h : Tendsto (fun n => ‖g n‖) atTop (nhds c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      |vectorMean (FilteredSequence D g z n)| ≤ c + ε :=
  filteredMeanDominated h

/-- **Filtered Std Domination wiring**: the filtered standard deviation is eventually
bounded in the infinite-width limit. -/
example (D : DimensionSequence) (g : D.GradientSequence) (z c : ℝ)
    (h : Tendsto (fun n => ‖g n‖) atTop (nhds c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      vectorStd (FilteredSequence D g z n) ≤ c + ε :=
  filteredStdDominated h

end LeanSharp.Tests
