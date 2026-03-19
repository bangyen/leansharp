/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.InfiniteLimit
import Mathlib.Data.Fintype.Basic

/-!
# Infinite Width Limit Tests

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

end LeanSharp.Tests
