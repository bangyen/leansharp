/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Theory.Dynamics.Convergence
import LeanSharp.Theory.Structural.ChainStability
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Chain-Level Convergence

This module extends the ZSharp convergence framework from single layers to
composed `Chain` architectures. A `Chain` flattens into a single parameter
space `W c.ParamDim` (via `Chain.ParamDimFintype`), so any strongly convex
smooth objective over the composed parameter space converges geometrically
under the ZSharp update — this is the network-level counterpart of the
single-layer convergence theorem.

## Main Definitions

* `ChainZSharpModel`: A `ZSharpModel` instantiated over a chain's flattened
  parameter space, with the chain's forward pass.

## Main Theorems

* `chain_zsharp_convergence`: Geometric convergence for objectives over the
  flattened parameter space of a chain.
* `chain_toLayer_forward`: The flattened chain forward equals `Chain.toLayer`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {In Out : Type} {c : Chain In Out}

/-- **Chain ZSharp Model**: A `ZSharpModel` over the flattened parameter space
`c.ParamDim` of a composed `Chain`. The forward pass is the chain's flattened
forward, so convergence of this model is convergence of the whole network. -/
structure ChainZSharpModel (c : Chain In Out) extends ZSharpModel c.ParamDim where
  /-- The forward pass of the chain, from parameters and input to output. -/
  forward : W c.ParamDim → In → Out
  /-- The chain's forward pass agrees with `Chain.toLayer`'s flattened forward. -/
  h_forward : forward = fun w x => (Chain.toLayer c).forward w x

/-- **Chain-to-Layer Forward Agreement**:
    The flattened forward pass of a chain equals the forward pass obtained by
    bundling the chain into a single `Layer` via `Chain.toLayer`. -/
theorem chain_toLayer_forward (w : W c.ParamDim) (x : In) :
    forwardChain (c.toData w) x = (Chain.toLayer c).forward w x :=
  rfl

/-- **Chain-Level ZSharp Convergence**: Any strongly convex smooth objective over
the flattened parameter space of a composed `Chain` converges geometrically to
its optimum under the ZSharp update, provided the learning-rate schedule satisfies
the local tightness condition. This is the network-level analogue of
`zsharp_convergence`. -/
theorem chain_zsharp_convergence (M : ChainZSharpModel c) (η : Schedule)
    (hη_tight : ∀ t, η t * (M.L.smoothness : ℝ) ^ 2 ≤ M.L.μ)
    (hμL : M.L.μ < (M.L.smoothness : ℝ)) :
    ZSharpConvergenceHolds M.L.toFun M.w_star η M.ρ M.z (M.L.smoothness : ℝ) M.L.μ := by
  exact zsharp_convergence M.toZSharpModel η hη_tight hμL

end LeanSharp
