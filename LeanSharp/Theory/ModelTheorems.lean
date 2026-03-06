/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs

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
    chain_data_norm_sq (backprop_chain z p x g_out).1 ≤
    chain_data_norm_sq (raw_backprop_chain p x g_out).1 := by
  -- Optimization: Generalize variables for induction to ensure ih is flexible.
  induction c generalizing x with
  | single L =>
      cases p with
      | single _ w =>
          unfold backprop_chain raw_backprop_chain chain_data_norm_sq
          simp only
          apply filtered_norm_bound_sq
  | append prev L ih =>
    cases p with
    | append p_prev w =>
        -- Stability for the current layer
        have h_L : ‖filtered_gradient (L.backward w (forward_chain p_prev x) g_out).1 z‖^2 ≤
                   ‖(L.backward w (forward_chain p_prev x) g_out).1‖^2 := by
          apply filtered_norm_bound_sq
        -- Inductive stability for the rest of the chain
        have h_prev := ih p_prev x (L.backward w (forward_chain p_prev x) g_out).2
        unfold backprop_chain raw_backprop_chain chain_data_norm_sq
        simp only
        exact add_le_add h_prev h_L

end LeanSharp
