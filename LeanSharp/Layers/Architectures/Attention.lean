/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import Mathlib.Analysis.InnerProductSpace.PiL2

import LeanSharp.Layers.Basic.Activation

namespace LeanSharp

/-!
# Multi-Head Attention

This module formalizes Multi-Head Attention (MHA) for sequence-based models.
It includes scaled dot-product attention (with Softmax) and the associated linear projections.

## Main definitions

* `attention_forward`: Scaled dot-product attention.
* `mha_layer`: A full Multi-Head Attention layer.
-/

variable {S D H : ℕ} [NeZero S] [NeZero D] [NeZero H]

/-- Parameter index for MHA: Query, Key, Value, and Output projections.
    Each projection is (D × D). -/
abbrev ATTParam (D : Type*) := (D × D) ⊕ (D × D) ⊕ (D × D) ⊕ (D × D)

/-- Scaled Dot-Product Attention (with row-wise Softmax).
    y = Softmax((Q Kᵀ) / √d) V -/
noncomputable def attention_forward (S D : ℕ) (Q K V : W (Fin S × Fin D)) : W (Fin S × Fin D) :=
  let scale := Real.sqrt (D : ℝ)
  let Q_f := WithLp.equiv 2 _ Q
  let K_f := WithLp.equiv 2 _ K
  let V_f := WithLp.equiv 2 _ V
  -- Pre-softmax scores A
  let A := fun (i j : Fin S) => (∑ k, Q_f (i, k) * K_f (j, k)) / scale
  -- Row-wise softmax
  let S_mat := fun (i j : Fin S) =>
    let row := WithLp.equiv 2 _ |>.symm fun j' => A i j'
    let row_s := WithLp.equiv 2 _ (softmax row)
    row_s j
  WithLp.equiv 2 (Fin S × Fin D → ℝ) |>.symm fun (i, d) =>
    ∑ j, S_mat i j * V_f (j, d)

/-- Scaled Dot-Product Attention backward pass. -/
noncomputable def attention_backward (S D : ℕ) (Q K V : W (Fin S × Fin D))
    (g_out : W (Fin S × Fin D)) : W (Fin S × Fin D) × W (Fin S × Fin D) × W (Fin S × Fin D) :=
  let scale := Real.sqrt (D : ℝ)
  let Q_f := WithLp.equiv 2 _ Q
  let K_f := WithLp.equiv 2 _ K
  let V_f := WithLp.equiv 2 _ V
  let g_out_f := WithLp.equiv 2 _ g_out
  -- Recompute A and Softmax(A)
  let A := fun (i j : Fin S) => (∑ k, Q_f (i, k) * K_f (j, k)) / scale
  let SM := fun (i j : Fin S) =>
    let row := WithLp.equiv 2 _ |>.symm fun j' => A i j'
    (WithLp.equiv 2 _ (softmax row)) j
  -- gV_jd = ∑_i g_out_id * SM_ij
  let gV := WithLp.equiv 2 _ |>.symm fun (j, d) => ∑ i, g_out_f (i, d) * SM i j
  -- gSM_ij = ∑_d g_out_id * V_jd
  let gSM := fun (i j : Fin S) => ∑ d, g_out_f (i, d) * V_f (j, d)
  -- gA_ij: backward through row-wise softmax
  let gA := fun (i j : Fin S) =>
    let row := WithLp.equiv 2 _ |>.symm fun j' => A i j'
    let g_row_out := WithLp.equiv 2 _ |>.symm fun j' => gSM i j'
    (WithLp.equiv 2 _ (softmax_backward row g_row_out)) j
  -- gQ_ik = ∑_j gA_ij * K_jk / scale
  let gQ := WithLp.equiv 2 _ |>.symm fun (i, k) => (∑ j, gA i j * K_f (j, k)) / scale
  -- gK_jk = ∑_i gA_ij * Q_ik / scale
  let gK := WithLp.equiv 2 _ |>.symm fun (j, k) => (∑ i, gA i j * Q_f (i, k)) / scale
  (gQ, gK, gV)

/-- Multi-Head Attention Layer instance.
    For simplicity, we formalize a single-head projection that maintains dimension. -/
noncomputable def mha_layer (S D : ℕ) : Layer (W (Fin S × Fin D)) (W (Fin S × Fin D)) where
  ParamDim := ATTParam (Fin D)
  fintypeParamDim := inferInstance
  forward w x :=
    let Q_p := (WithLp.equiv 2 (Fin D × Fin D → ℝ) |>.symm fun p =>
      (WithLp.equiv 2 _ w) (Sum.inl p))
    let K_p := (WithLp.equiv 2 (Fin D × Fin D → ℝ) |>.symm fun p =>
      (WithLp.equiv 2 _ w) (Sum.inr (Sum.inl p)))
    let V_p := (WithLp.equiv 2 (Fin D × Fin D → ℝ) |>.symm fun p =>
      (WithLp.equiv 2 _ w) (Sum.inr (Sum.inr (Sum.inl p))))
    -- Projections
    let Q := WithLp.equiv 2 (Fin S × Fin D → ℝ) |>.symm fun p =>
      ∑ k, (WithLp.equiv 2 _ x) (p.1, k) * Q_p (k, p.2)
    let K := WithLp.equiv 2 (Fin S × Fin D → ℝ) |>.symm fun p =>
      ∑ k, (WithLp.equiv 2 _ x) (p.1, k) * K_p (k, p.2)
    let V := WithLp.equiv 2 (Fin S × Fin D → ℝ) |>.symm fun p =>
      ∑ k, (WithLp.equiv 2 _ x) (p.1, k) * V_p (k, p.2)
    attention_forward S D Q K V
  backward w x g_out :=
    let Q_p_f := WithLp.equiv 2 _ (WithLp.equiv 2 (Fin D × Fin D → ℝ) |>.symm fun p =>
      (WithLp.equiv 2 _ w) (Sum.inl p))
    let K_p_f := WithLp.equiv 2 _ (WithLp.equiv 2 (Fin D × Fin D → ℝ) |>.symm fun p =>
      (WithLp.equiv 2 _ w) (Sum.inr (Sum.inl p)))
    let V_p_f := WithLp.equiv 2 _ (WithLp.equiv 2 (Fin D × Fin D → ℝ) |>.symm fun p =>
      (WithLp.equiv 2 _ w) (Sum.inr (Sum.inr (Sum.inl p))))
    let x_f := WithLp.equiv 2 _ x
    -- Recompute projected Q, K, V for backward
    let Q := WithLp.equiv 2 _ |>.symm fun p => ∑ k, x_f (p.1, k) * Q_p_f (k, p.2)
    let K := WithLp.equiv 2 _ |>.symm fun p => ∑ k, x_f (p.1, k) * K_p_f (k, p.2)
    let V := WithLp.equiv 2 _ |>.symm fun p => ∑ k, x_f (p.1, k) * V_p_f (k, p.2)
    let (gQ, gK, gV) := attention_backward S D Q K V g_out
    let gQ_f := WithLp.equiv 2 _ gQ
    let gK_f := WithLp.equiv 2 _ gK
    let gV_f := WithLp.equiv 2 _ gV
    -- Gradients w.r.t projection weights
    let gQ_p := fun (k d : Fin D) => ∑ s, x_f (s, k) * gQ_f (s, d)
    let gK_p := fun (k d : Fin D) => ∑ s, x_f (s, k) * gK_f (s, d)
    let gV_p := fun (k d : Fin D) => ∑ s, x_f (s, k) * gV_f (s, d)
    let g_w := WithLp.equiv 2 _ |>.symm fun
      | Sum.inl p => gQ_p p.1 p.2
      | Sum.inr (Sum.inl p) => gK_p p.1 p.2
      | Sum.inr (Sum.inr (Sum.inl p)) => gV_p p.1 p.2
      | Sum.inr (Sum.inr (Sum.inr _)) => 0 -- Unused projection (e.g. output)

    -- Gradient w.r.t input x
    let g_x := WithLp.equiv 2 _ |>.symm fun (s, k) =>
      (∑ d, gQ_f (s, d) * Q_p_f (k, d)) +
      (∑ d, gK_f (s, d) * K_p_f (k, d)) +
      (∑ d, gV_f (s, d) * V_p_f (k, d))
    (g_w, g_x)

end LeanSharp
