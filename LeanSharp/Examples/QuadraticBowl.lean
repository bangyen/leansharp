/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Objective
import LeanSharp.Theory.Dynamics.Convergence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

/-!
# Quadratic Bowl Example

This module provides a concrete demonstration of the ZSharp algorithm on a
simple 2D quadratic landscape. It verifies that the abstract definitions
in `W ι` can be explicitly evaluated on Euclidean vectors.

## Main definitions

* `L_toy`: A simple 2D quadratic loss function $L(w_0, w_1) = w_0^2 + w_1^2$.
* `exactGradientToy`: The explicit analytical gradient of `L_toy`.
* `wInit`: A concrete initial weight vector $[1, 3]$.

## Main theorems

This module intentionally exposes definitions only; concrete toy equalities and
one-step checks are kept in `Tests/Landscape/QuadraticBowl.lean`.
-/

namespace LeanSharp.QuadraticBowl

open BigOperators

-- We work in 2D space
local notation "W2" => W (Fin 2)

/-- A simple 2D quadratic loss function $L(w_0, w_1) = w_0^2 + w_1^2$. -/
noncomputable def L_toy (w : W2) : ℝ :=
  let w0 := (WithLp.equiv 2 (Fin 2 → ℝ) w) 0
  let w1 := (WithLp.equiv 2 (Fin 2 → ℝ) w) 1
  w0^2 + w1^2

/-- The analytical gradient of `L_toy` is $\nabla L(w) = [2w_0, 2w_1]$. -/
noncomputable def exactGradientToy (w : W2) : W2 :=
  WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun i =>
    2 * (WithLp.equiv 2 (Fin 2 → ℝ) w) i

/-- Concrete initial weight vector: $w = [1, 3]$. -/
noncomputable def wInit : W2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i => if i = 0 then 1 else 3)

/-- **Toy Perturbation**: For the quadratic bowl at $w=[1, 3]$, the perturbation
direction is aligned with the gradient $[2, 6]$. -/
noncomputable def toyPerturbation (ρ : ℝ) : W2 :=
  samPerturbation L_toy wInit ρ

end LeanSharp.QuadraticBowl
