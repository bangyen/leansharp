/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Taylor.SmoothDescent

/-!
# Taylor Sobolev-Compatible Descent

This module exists to expose `H¹`-aware descent interfaces while reusing the
core smoothness descent theorem from `SmoothDescent`.

## Definitions

* `HasWeakGradientCore`: weak-gradient contract for core Taylor interfaces.
* `H1SmoothObjective`: `H¹`-aware smooth objective bundle.

## Theorems

* `smoothObjective_hasWeakGradientCore`: canonical weak-gradient witness.
* `smooth_descent_h1`: `H¹`-aware descent lemma variant.
-/

namespace LeanSharp

open InnerProductSpace Real NNReal

variable {ι : Type*} [Fintype ι]

/-- Core weak-gradient contract: this predicate exists to let Taylor lemmas
accept weak-derivative style assumptions without importing higher-level
functional-analysis modules. -/
def HasWeakGradientCore (u : W ι → ℝ) (grad_u : W ι → W ι) : Prop :=
  ∀ x, HasFDerivAt u ((InnerProductSpace.toDual ℝ (W ι)) (grad_u x)) x

/-- `H¹`-aware smooth objective bundle used by core Taylor descent lemmas. It
stores weak-gradient data and a proof that this weak gradient agrees with the
canonical `gradient`, so existing smooth-descent proofs can be reused internally. -/
structure H1SmoothObjective (ι : Type*) [Fintype ι] where
  /-- The underlying loss function. -/
  toFun : W ι → ℝ
  /-- The smoothness constant. -/
  smoothness : ℝ≥0
  /-- Differentiability hypothesis for the loss. -/
  differentiable : Differentiable ℝ toFun
  /-- A weak-gradient field for the objective. -/
  weakGradient : W ι → W ι
  /-- Weak-gradient witness for `weakGradient`. -/
  hasWeakGradient : HasWeakGradientCore toFun weakGradient
  /-- Weak-gradient field is `L`-Lipschitz. -/
  weakLipschitz : LipschitzWith smoothness weakGradient
  /-- Compatibility with the canonical `gradient` field. -/
  gradient_eq_weakGradient : gradient toFun = weakGradient

/-- Canonical weak-gradient witness for a `SmoothObjective` using its standard
gradient field. -/
theorem smoothObjective_hasWeakGradientCore (L : SmoothObjective ι) :
    HasWeakGradientCore L.toFun (gradient L.toFun) := by
  intro x
  simpa only [gradient, LinearIsometryEquiv.apply_symm_apply] using
    (L.differentiable x).hasFDerivAt

/-- Compatibility constructor from `SmoothObjective` to `H1SmoothObjective`. -/
noncomputable def SmoothObjective.toH1SmoothObjective
    (L : SmoothObjective ι) : H1SmoothObjective ι :=
  { toFun := L.toFun
    smoothness := L.smoothness
    differentiable := L.differentiable
    weakGradient := gradient L.toFun
    hasWeakGradient := smoothObjective_hasWeakGradientCore L
    weakLipschitz := by simpa only using L.lipschitz
    gradient_eq_weakGradient := rfl }

/-- **`H¹`-Aware L-smooth descent**: this variant accepts a weak-gradient
contract in addition to smoothness assumptions, then reduces to the canonical
smooth-descent theorem via compatibility between weak and standard gradients. -/
theorem smooth_descent_h1 (L : H1SmoothObjective ι) (w ε : W ι) :
    L.toFun (w + ε) ≤
      L.toFun w + inner ℝ (gradient L.toFun w) ε + (L.smoothness : ℝ) / 2 * ‖ε‖ ^ 2 := by
  let Lsmooth : SmoothObjective ι :=
    { toFun := L.toFun
      smoothness := L.smoothness
      differentiable := L.differentiable
      lipschitz := by
        simpa only [L.gradient_eq_weakGradient] using L.weakLipschitz }
  exact smooth_descent Lsmooth w ε

end LeanSharp
