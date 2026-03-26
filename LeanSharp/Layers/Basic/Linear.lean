/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Theory.Alignment
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Linear Layers

This module formalizes linear (affine) layers $y = Wx + b$ within the `Layer` framework.

## Main definitions

* `linearLayer`: A layer representing an affine transformation.
* `LinearParam`: The parameter index type for weights and biases.
* `linear_forward_lipschitz`: Lipshitz continuity of the forward pass.

## Theorems

* `linear_forward_lipschitz`.
-/

namespace LeanSharp

open BigOperators

variable {ι_in ι_out : Type} [Fintype ι_in] [Fintype ι_out]

/-- The parameter index type for a linear layer: (output_dim × input_dim) for weights,
and output_dim for biases. -/
abbrev LinearParam (ι_in ι_out : Type) := (ι_out × ι_in) ⊕ ι_out

instance [Fintype ι_in] [Fintype ι_out] : Fintype (LinearParam ι_in ι_out) :=
  inferInstance

/-- The forward pass $y = Wx + b$. -/
noncomputable def linearForward (w : W (LinearParam ι_in ι_out)) (x : W ι_in) : W ι_out :=
  WithLp.equiv 2 (ι_out → ℝ) |>.symm fun i =>
    (∑ j, (WithLp.equiv 2 _ w) (Sum.inl (i, j)) * (WithLp.equiv 2 _ x) j) +
    (WithLp.equiv 2 _ w) (Sum.inr i)

/-- The backward pass for a linear layer.
    Returns (gradient w.r.t parameters, gradient w.r.t input). -/
noncomputable def linearBackward (w : W (LinearParam ι_in ι_out)) (x : W ι_in)
    (g_out : W ι_out) :
    W (LinearParam ι_in ι_out) × W ι_in :=
  let g_w := WithLp.equiv 2 _ |>.symm fun
    | Sum.inl (i, j) => (WithLp.equiv 2 _ g_out) i * (WithLp.equiv 2 _ x) j
    | Sum.inr i => (WithLp.equiv 2 _ g_out) i
  let g_x := WithLp.equiv 2 _ |>.symm fun j =>
    ∑ i, (WithLp.equiv 2 _ w) (Sum.inl (i, j)) * (WithLp.equiv 2 _ g_out) i
  (g_w, g_x)

/-- Construct a linear layer instance. -/
noncomputable def linearLayer (ι_in ι_out : Type) [Fintype ι_in] [Fintype ι_out] :
    Layer (W ι_in) (W ι_out) where
  ParamDim := LinearParam ι_in ι_out
  fintypeParamDim := inferInstance
  forward := linearForward
  backward := linearBackward

/-- **Linear Forward Lipschitz**: The linear layer's forward pass $y = Wx + b$
    is Lipschitz continuous for any fixed weights and biases. -/
theorem linear_forward_lipschitz (w : W (LinearParam ι_in ι_out)) :
    ∃ K, LipschitzWith K (linearForward w) := by
  classical
  let L : W ι_in →ₗ[ℝ] W ι_out :=
    (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp <|
    (Matrix.toLin' (Matrix.of fun (i : ι_out) (j : ι_in) =>
      (WithLp.equiv 2 _ w) (Sum.inl (i, j)))).comp <|
    (WithLp.linearEquiv 2 ℝ _).toLinearMap
  let b : W ι_out :=
    (WithLp.linearEquiv 2 ℝ _).symm fun i => (WithLp.equiv 2 _ w) (Sum.inr i)
  have h_affine (x : W ι_in) :
      linearForward w x = L x + b := by
    ext i
    simp only [
      linearForward,
      WithLp.equiv_apply,
      WithLp.equiv_symm_apply,
      LinearMap.comp_apply,
      LinearEquiv.coe_coe,
      WithLp.linearEquiv_apply,
      AddEquiv.toEquiv_eq_coe,
      Equiv.toFun_as_coe,
      EquivLike.coe_coe,
      WithLp.addEquiv_apply,
      Matrix.toLin'_apply,
      WithLp.linearEquiv_symm_apply,
      Equiv.invFun_as_coe,
      AddEquiv.coe_toEquiv_symm,
      WithLp.addEquiv_symm_apply,
      PiLp.add_apply,
      Matrix.mulVec,
      Matrix.of_apply,
      add_left_inj,
      L,
      b
    ]
    rfl
  let LC := L.toContinuousLinearMap
  use ‖LC‖₊
  apply LipschitzWith.of_dist_le_mul; intro x₁ x₂
  rw [h_affine, h_affine, dist_add_right]
  exact LC.lipschitz.dist_le_mul x₁ x₂

/-- **Linear Forward Smoothness**: Linear layers are $C^\infty$ (and thus $C^2$). -/
theorem contDiff_linearForward (w : W (LinearParam ι_in ι_out)) :
    ContDiff ℝ 2 (linearForward w) := by
  classical
  let L : W ι_in →ₗ[ℝ] W ι_out :=
    (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp <|
    (Matrix.toLin' (Matrix.of fun (i : ι_out) (j : ι_in) =>
      (WithLp.equiv 2 _ w) (Sum.inl (i, j)))).comp <|
    (WithLp.linearEquiv 2 ℝ _).toLinearMap
  let b : W ι_out :=
    (WithLp.linearEquiv 2 ℝ _).symm fun i => (WithLp.equiv 2 _ w) (Sum.inr i)
  have h_affine (x : W ι_in) :
      linearForward w x = L x + b := by
    ext i
    simp only [linearForward, L, b]
    rfl
  rw [funext h_affine]
  apply ContDiff.add
  · apply (L.toContinuousLinearMap).contDiff
  · exact contDiff_const

/-- **Linear Stability Certificate**: Bundles the linear layer's forward pass
    with its Lipschitz constant and $C^2$ smoothness proof. -/
noncomputable def linearCertificate (w : W (LinearParam ι_in ι_out)) :
    StabilityCertificate (W ι_in) (W ι_out) where
  f := linearForward w
  K := (linear_forward_lipschitz w).choose
  h_lipschitz := (linear_forward_lipschitz w).choose_spec
  h_smooth := contDiff_linearForward w

end LeanSharp
