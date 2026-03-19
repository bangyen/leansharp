/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Layers.Basic.Activation
import LeanSharp.Layers.Basic.Linear
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Real.Sqrt

/-!
# 2-Layer MLP Example

This module implements a standard 2-layer Multi-Layer Perceptron (MLP).
It also establishes Lipschitz stability markers for the architecture.

## Main Definitions
* `mlp2Layer`.

## Main Theorems
* `mlp_forward_stability`.
-/

namespace LeanSharp

variable {ι_in ι_mid ι_out : Type} [Fintype ι_in] [Fintype ι_mid] [Fintype ι_out]

/-- A standard 2-layer MLP: Linear -> ReLU -> Linear. -/
noncomputable def mlp2Layer (ι_in ι_mid ι_out : Type)
    [Fintype ι_in] [Fintype ι_mid] [Fintype ι_out] :
    Chain (W ι_in) (W ι_out) :=
  Chain.append (Chain.append (Chain.single (linearLayer ι_in ι_mid))
    (reluLayer ι_mid)) (linearLayer ι_mid ι_out)

/-- **MLP Forward Stability**: The 2-layer MLP is Lipschitz continuous in its input
    for fixed parameters. Proved via composition of Lipschitz layers. -/
theorem mlp_forward_stability (p : ChainData (mlp2Layer ι_in ι_mid ι_out)) :
    ∃ K, LipschitzWith K (fun x => forwardChain p x) := by
  match p with
  | .append p_relu_linear w2 =>
    match p_relu_linear with
    | .append p_linear w_relu =>
      match p_linear with
      | .single _ w1 =>
        -- MLP(x) = Linear2(ReLU(Linear1(x)))
        have h1 : ∃ K : NNReal,
            LipschitzWith K (fun x => (linearLayer ι_in ι_mid).forward w1 x) :=
          linear_forward_lipschitz w1
        have h2 : LipschitzWith 1 (fun x => (reluLayer ι_mid).forward w_relu x) :=
          relu_lipschitz
        have h3 : ∃ K : NNReal,
            LipschitzWith K (fun x => (linearLayer ι_mid ι_out).forward w2 x) :=
          linear_forward_lipschitz w2
        rcases h1 with ⟨K1, h1L⟩
        rcases h3 with ⟨K3, h3L⟩
        use K3 * (1 : NNReal) * K1
        convert h3L.comp (h2.comp h1L) using 1
        · rw [mul_one, one_mul]

/-- Verification that the MLP chain can be evaluated. -/
noncomputable example (p : ChainData (mlp2Layer ι_in ι_mid ι_out)) (x : W ι_in) : W ι_out :=
  forwardChain p x

end LeanSharp
