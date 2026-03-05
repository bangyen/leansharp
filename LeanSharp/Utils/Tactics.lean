/-
Copyright (c) 2024 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import Mathlib.Tactic

/-!
# ZSharp Tactics

This module defines custom tactics to automate the repetitive parts of
convergence and contraction proofs in ZSharp.

The main tactic is `zsharp_solve`, which:
1. Applies specific Z-score filtering lemmas.
2. Uses `positivity` to resolve non-negativity side-goals.
3. Uses `linarith` or `aesop` for final inequality resolution.
-/

namespace LeanSharp

/--
`zsharp_solve` is a powerful tactic for proving inequalities involving
filtered gradients and norm contractions.
-/
macro "zsharp_solve" : tactic => `(tactic| (
  simp only [filtered_gradient, z_score_mask, hadamard] at *
  try positivity
  try linarith
  try aesop
))

end LeanSharp
