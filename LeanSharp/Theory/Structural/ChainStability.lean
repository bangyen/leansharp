/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

/-!
# Deep Model Stability Theorems

This module formalizes the collective stability of Z-score filtered gradients
across multi-layer neural network chains.

## Main theorems

* `zsharp_chain_stability`: Proves that layer-wise Z-score filtering ensures
  that the total norm of the filtered parameter updates is bounded by the total
  norm of the raw gradients.
-/

namespace LeanSharp

/-- **Chain-wise Stability**: For any neural network chain, applying Z-score
filtering layer-wise results in a total parameter update whose norm is bounded
by the norm of the raw (unfiltered) backpropagation gradients. -/
theorem zsharp_chain_stability {In Out : Type} (c : Chain In Out)
    (z : ℝ) (p : ChainData c) (x : In) (g_out : Out) :
    chainDataNormSq (backpropChain z p x g_out).1 ≤
    chainDataNormSq (rawBackpropChain p x g_out).1 := by
  induction c generalizing x with
  | single L =>
      cases p
      unfold backpropChain rawBackpropChain chainDataNormSq
      simp only [norm_sq_filtered_gradient_le]
  | append prev L ih =>
    cases p with | append p_prev w =>
    unfold backpropChain rawBackpropChain chainDataNormSq
    apply add_le_add (ih p_prev _ _) (norm_sq_filtered_gradient_le _ _)

end LeanSharp
