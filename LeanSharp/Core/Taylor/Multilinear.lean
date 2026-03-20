/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Taylor

/-!
# Multilinear Taylor Expansion

This module exists to provide a generalized, arbitrary-degree Taylor expansion
bound. It generalizes the first-order L-smoothness bounds natively to `n`-th
order multilinear forms.

## Definitions

* `SmoothObjectiveN`: n-th order smooth function bundle.
* `HKSmoothObjectiveN`: `H^k`-aware n-th order smooth bundle.

## Theorems

* `multilinear_taylor_bound`: $n$-th order Taylor bound on the objective.
-/

namespace LeanSharp

open Set InnerProductSpace Real NNReal

variable {ι : Type*} [Fintype ι]

/-- A structure bundling a function `L` with generalized n-th order smoothness. -/
structure SmoothObjectiveN (ι : Type*) [Fintype ι] (n : ℕ) where
  /-- The underlying loss function. -/
  toFun : W ι → ℝ
  /-- The n-th order smoothness constant. -/
  smoothness : ℝ≥0
  /-- Proof that the loss is n-times continuously differentiable. -/
  iterated_differentiable : ContDiff ℝ n toFun
  /-- Global bound on the n-th directional derivative along any segment.
      This directional formulation avoids Faa Di Bruno combination explosion. -/
  bound : ∀ (w ε : W ι) (y : ℝ), y ∈ Icc (0:ℝ) 1 →
    ‖iteratedDerivWithin n (fun t => toFun (w + t • ε)) (Icc 0 1) y‖ ≤ smoothness * ‖ε‖ ^ n

/-- `H^k`-aware n-th order smooth objective bundle. This wrapper exists to let
Taylor bounds be stated against Sobolev-style regularity contracts while
remaining backward-compatible with existing `SmoothObjectiveN` clients. -/
structure HKSmoothObjectiveN (ι : Type*) [Fintype ι] (n k : ℕ) where
  /-- Underlying n-th order smooth objective data. -/
  toSmoothObjectiveN : SmoothObjectiveN ι n
  /-- `H^k` regularity contract placeholder used by higher-level interfaces. -/
  hkRegularity : Prop

instance {n : ℕ} : CoeFun (SmoothObjectiveN ι n) (fun _ => W ι → ℝ) where
  coe L := L.toFun

/-- Generalized Multilinear Expansion Descent Lemma.
Bounds the approximation error of a function evaluated at $w + ε$
to the $n$-th order factorial remainder. -/
theorem multilinear_taylor_bound (n : ℕ) (L : SmoothObjectiveN ι (n + 1)) (w ε : W ι) :
    ‖L.toFun (w + ε) - taylorWithinEval (fun t => L.toFun (w + t • ε)) n (Icc 0 1) 0 1‖ ≤
      (L.smoothness : ℝ) * ‖ε‖ ^ (n + 1) / (n.factorial : ℝ) := by
  let φ : ℝ → ℝ := fun t => L.toFun (w + t • ε)
  have h_cont_diff : ContDiffOn ℝ (n + 1) φ (Icc 0 1) := by
    apply ContDiff.contDiffOn
    exact L.iterated_differentiable.comp (by fun_prop)
  have h_bound : ∀ y ∈ Icc (0:ℝ) 1,
      ‖iteratedDerivWithin (n + 1) φ (Icc 0 1) y‖ ≤ (L.smoothness : ℝ) * ‖ε‖ ^ (n + 1) := by
    exact L.bound w ε
  have h_taylor := taylor_mean_remainder_bound zero_le_one h_cont_diff
    (right_mem_Icc.mpr zero_le_one) h_bound
  have h_eval : φ 1 = L.toFun (w + ε) := by simp only [φ, one_smul]
  rw [← h_eval]
  have h_rhs : (L.smoothness : ℝ) * ‖ε‖ ^ (n + 1) * (1 - 0) ^ (n + 1) / (n.factorial : ℝ) =
      (L.smoothness : ℝ) * ‖ε‖ ^ (n + 1) / (n.factorial : ℝ) := by ring
  linarith [h_taylor]

end LeanSharp
