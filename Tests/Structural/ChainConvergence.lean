/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Theory.Dynamics.ChainConvergence

/-!
# Chain-Level Convergence Tests

This module verifies that a `Chain`'s flattened parameter space supports the
ZSharp convergence framework, and that the chain forward agrees with the
`Chain.toLayer` bridge.

## Examples

* `test_chain_paramdim_convergence_interface`.
* `test_chain_to_layer_forward_interface`.
-/

namespace LeanSharp.Tests

open ProbabilityTheory MeasureTheory

/-- **Chain parameter-space convergence wiring**: a `ChainZSharpModel` over a chain's
flattened parameter space yields geometric convergence under the ZSharp update. -/
example {In Out : Type} (c : Chain In Out) (M : ChainZSharpModel c) (η : Schedule)
    (hη_tight : ∀ t, η t * (M.L.smoothness : ℝ) ^ 2 ≤ M.L.μ)
    (hμL : M.L.μ < (M.L.smoothness : ℝ)) :
    ZSharpConvergenceHolds M.L.toFun M.w_star η M.ρ M.z (M.L.smoothness : ℝ) M.L.μ :=
  chain_zsharp_convergence M η hη_tight hμL

/-- **Chain-to-layer forward wiring**: the flattened chain forward agrees with the
`Chain.toLayer` bridge. -/
example {In Out : Type} (c : Chain In Out) (w : W c.ParamDim) (x : In) :
    forwardChain (c.toData w) x = (Chain.toLayer c).forward w x :=
  chain_toLayer_forward w x

end LeanSharp.Tests
