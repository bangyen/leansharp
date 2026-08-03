/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Layers.Architectures.Transformer

/-!
# Architecture Tests

This module verifies architectural invariants for complex models like
Transformers.

## Examples
-/

namespace LeanSharp.Tests

/-- Test: Transformer Encoder Block structure verifies as a chain of length 2. -/
example (S D D_ff : ℕ) [NeZero S] [NeZero D] :
    (transformerEncoderBlock S D D_ff).length = 2 :=
  rfl

/-- Test: Transformer Encoder Block input/output types. -/
example (S D D_ff : ℕ) [NeZero S] [NeZero D] :
    Nonempty (Chain (W (Fin S × Fin D)) (W (Fin S × Fin D))) := by
  exact ⟨transformerEncoderBlock S D D_ff⟩

end LeanSharp.Tests
