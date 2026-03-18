/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Aesop
import Lean
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
    simp (config := {zeta := false}) only [
      filteredGradient,
      zScoreMask,
      hadamard,
      ge_iff_le,
      gt_iff_lt
    ] at *
    simp only [WithLp.equiv_apply, Equiv.apply_symm_apply] at *
    try split_ifs
    all_goals
      try (simp [*] at *) -- no_squeeze
      try (repeat' split)
      try positivity
      try linarith
      try aesop
  ))

end LeanSharp
