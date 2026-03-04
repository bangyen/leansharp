import LeanSharp.Landscape
import LeanSharp.Sam
import LeanSharp.Filters

/-!
# LeanSharp

This is the main entry point for the `LeanSharp` mathematical formalization
of Sharpness-Aware Minimization with Z-Score Gradient Filtering.

Everything defined so far is fully compiled and type-checked by Lean 4's kernel!

## Basic Properties

Let's prove a very simple lemma about our `z_score_mask`.
Any value in the mask array is either 0 or 1.
-/

variable {d : ℕ}

/-- The elements of the z-score mask are strictly binary (either `0` or `1`). -/
theorem z_score_mask_binary (g : W d) (z : ℝ) (i : Fin d) :
    z_score_mask g z i = 0 ∨ z_score_mask g z i = 1 := by
  -- `z_score_mask` is defined as an `if ... then 1 else 0` expression
  unfold z_score_mask
  -- Simplify the space equivalence wrapper first so the if statement is exposed
  dsimp [WithLp.equiv]
  -- Lean has a built-in tactic to split on if-then-else conditions
  split_ifs
  -- Case 1: The condition is true, so the value is 1
  · right; rfl
  -- Case 2: The condition is false, so the value is 0
  · left; rfl
