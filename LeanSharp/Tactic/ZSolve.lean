/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Lean
import Aesop
import LeanSharp.Core.Filters
import LeanSharp.Core.Stats

/-!
# The `zsharp_solve` Tactic

This module defines a custom tactic for automating algebraic proofs involving
Z-score gradient filtering. It leverages `aesop` with a specialized rule set.
-/

namespace LeanSharp

/-- Standard unfolding rules for Z-score definitions. -/
syntax "zsharp_solve" : tactic

macro_rules
  | `(tactic| zsharp_solve) => `(tactic| (
    simp (config := {zeta := false}) only [filtered_gradient,
      z_score_mask, hadamard] at *
    simp only [WithLp.equiv_apply, Equiv.apply_symm_apply] at *
    try split_ifs <;> try (simp at *; linarith)
    try positivity
    try linarith
    try aesop
  ))

end LeanSharp
