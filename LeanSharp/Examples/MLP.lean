/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.LinearLayer
import LeanSharp.Core.Activation

/-!
# 2-Layer MLP Example

This module implements a standard 2-layer Multi-Layer Perceptron (MLP).
-/

namespace LeanSharp

variable {ι_in ι_mid ι_out : Type} [Fintype ι_in] [Fintype ι_mid] [Fintype ι_out]

/-- A standard 2-layer MLP: Linear -> ReLU -> Linear. -/
noncomputable def mlp_2_layer (ι_in ι_mid ι_out : Type)
    [Fintype ι_in] [Fintype ι_mid] [Fintype ι_out] :
    Chain (W ι_in) (W ι_out) :=
  Chain.append (Chain.append (Chain.single (linear_layer ι_in ι_mid))
    (relu_layer ι_mid)) (linear_layer ι_mid ι_out)

/-- Verification that the MLP chain can be evaluated. -/
noncomputable example (p : ChainData (mlp_2_layer ι_in ι_mid ι_out)) (x : W ι_in) : W ι_out :=
  forward_chain p x

end LeanSharp
