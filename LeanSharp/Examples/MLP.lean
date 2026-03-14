/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Layers.Basic.Activation
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# 2-Layer MLP Example

This module implements a standard 2-layer Multi-Layer Perceptron (MLP).
It also establishes Lipschitz stability markers for the architecture.
-/

namespace LeanSharp

variable {ι_in ι_mid ι_out : Type} [Fintype ι_in] [Fintype ι_mid] [Fintype ι_out]

/-- A standard 2-layer MLP: Linear -> ReLU -> Linear. -/
noncomputable def mlp_2_layer (ι_in ι_mid ι_out : Type)
    [Fintype ι_in] [Fintype ι_mid] [Fintype ι_out] :
    Chain (W ι_in) (W ι_out) :=
  Chain.append (Chain.append (Chain.single (linear_layer ι_in ι_mid))
    (relu_layer ι_mid)) (linear_layer ι_mid ι_out)

/-- **MLP Forward Stability**: The 2-layer MLP is Lipschitz continuous in its input
    for fixed parameters. Proved via composition of Lipschitz layers. -/
theorem mlp_forward_stability (p : ChainData (mlp_2_layer ι_in ι_mid ι_out)) :
    ∃ K, LipschitzWith K (fun x => forward_chain p x) := by
  match p with
  | .append p_relu_linear w2 =>
    match p_relu_linear with
    | .append p_linear w_relu =>
      match p_linear with
      | .single _ w1 =>
        -- MLP(x) = Linear2(ReLU(Linear1(x)))
        have h1 : ∃ K : NNReal,
            LipschitzWith K (fun x => (linear_layer ι_in ι_mid).forward w1 x) := by
          classical
          let L : W ι_in →ₗ[ℝ] W ι_mid :=
            (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp <|
            (Matrix.toLin' (Matrix.of fun (i : ι_mid) (j : ι_in) =>
              (WithLp.equiv 2 _ w1) (Sum.inl (i, j)))).comp <|
            (WithLp.linearEquiv 2 ℝ _).toLinearMap
          let b : W ι_mid :=
            (WithLp.linearEquiv 2 ℝ _).symm fun i => (WithLp.equiv 2 _ w1) (Sum.inr i)
          have h_affine (x : W ι_in) :
              (linear_layer ι_in ι_mid).forward w1 x = L x + b := by
            ext i
            simp only [
              linear_layer,
              linear_forward,
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
          have hL := LC.lipschitz
          apply LipschitzWith.of_dist_le_mul; intro x y
          rw [h_affine, h_affine, dist_add_right]
          exact hL.dist_le_mul x y
        have h2 : LipschitzWith 1 (fun x => (relu_layer ι_mid).forward w_relu x) := by
          apply LipschitzWith.of_dist_le_mul
          intro x y
          simp only [
            relu_layer,
            relu,
            WithLp.equiv_apply,
            WithLp.equiv_symm_apply,
            NNReal.coe_one,
            one_mul
          ]
          rw [PiLp.dist_eq_of_L2, PiLp.dist_eq_of_L2]
          apply Real.sqrt_le_sqrt
          apply Finset.sum_le_sum
          intro i _
          rw [sq_le_sq, abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg]
          rw [Real.dist_eq, Real.dist_eq]
          exact (abs_max_sub_max_le_max 0 (x.ofLp i) 0 (y.ofLp i)).trans
            (by simp only [sub_self, abs_zero, abs_nonneg, sup_of_le_right, le_refl])
        have h3 : ∃ K : NNReal,
            LipschitzWith K (fun x => (linear_layer ι_mid ι_out).forward w2 x) := by
          classical
          let L : W ι_mid →ₗ[ℝ] W ι_out :=
            (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp <|
            (Matrix.toLin' (Matrix.of fun (i : ι_out) (j : ι_mid) =>
              (WithLp.equiv 2 _ w2) (Sum.inl (i, j)))).comp <|
            (WithLp.linearEquiv 2 ℝ _).toLinearMap
          let b : W ι_out :=
            (WithLp.linearEquiv 2 ℝ _).symm fun i => (WithLp.equiv 2 _ w2) (Sum.inr i)
          have h_affine (x : W ι_mid) :
              (linear_layer ι_mid ι_out).forward w2 x = L x + b := by
            ext i
            simp only [
              linear_layer,
              linear_forward,
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
          have hL := LC.lipschitz
          apply LipschitzWith.of_dist_le_mul; intro x y
          rw [h_affine, h_affine, dist_add_right]
          exact hL.dist_le_mul x y
        rcases h1 with ⟨K1, h1L⟩
        rcases h3 with ⟨K3, h3L⟩
        use K3 * (1 : NNReal) * K1
        convert h3L.comp (h2.comp h1L) using 1
        · rw [mul_one, one_mul]

/-- Verification that the MLP chain can be evaluated. -/
noncomputable example (p : ChainData (mlp_2_layer ι_in ι_mid ι_out)) (x : W ι_in) : W ι_out :=
  forward_chain p x

end LeanSharp
