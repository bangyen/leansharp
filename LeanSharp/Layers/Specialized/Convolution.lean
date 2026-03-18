/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models

/-!
# CNN Foundations

This module formalizes 2D Convolution and Pooling layers.

## Main definitions

* `conv2d_layer`: A 2D Convolutional layer.
* `maxPoolingLayer`: A Max Pooling layer.
* `ConvParam`: Parameter index type for convolution kernels and biases.
-/

namespace LeanSharp

open BigOperators

/-- Parameter index type for 2D Convolution: kernel weights and a single bias. -/
abbrev ConvParam (kH kW : ℕ) := (Fin kH × Fin kW) ⊕ Unit

/-- Simplified Conv2D forward pass.
    Maps a flattened input to a flattened output using a sliding window. -/
noncomputable def conv2d_forward (h w kh kw : ℕ) (h_h : kh ≤ h) (h_w : kw ≤ w)
    (Wp : W (ConvParam kh kw)) (x : W (Fin h × Fin w)) : W (Fin (h - kh + 1) × Fin (w - kw + 1)) :=
  let h' := h - kh + 1
  let w' := w - kw + 1
  WithLp.equiv 2 (Fin h' × Fin w' → ℝ) |>.symm fun p =>
    let (i, j) := p
    let kernel_sum := ∑ m : Fin kh, ∑ n : Fin kw,
      (WithLp.equiv 2 _ Wp) (Sum.inl (m, n)) *
      (WithLp.equiv 2 _ x) (⟨i.val + m.val, by
                              have hi := i.is_lt; have hm := m.is_lt
                              dsimp only [h'] at hi; omega⟩,
                            ⟨j.val + n.val, by
                              have hj := j.is_lt; have hn := n.is_lt
                              dsimp only [w'] at hj; omega⟩)
    let bias := (WithLp.equiv 2 _ Wp) (Sum.inr ())
    kernel_sum + bias

/-- Simplified Conv2D backward pass. -/
noncomputable def conv2d_backward (h w kh kw : ℕ) (h_h : kh ≤ h) (h_w : kw ≤ w)
    (Wp : W (ConvParam kh kw)) (x : W (Fin h × Fin w))
    (g_out : W (Fin (h - kh + 1) × Fin (w - kw + 1))) :
    W (ConvParam kh kw) × W (Fin h × Fin w) :=
  let h' := h - kh + 1
  let w' := w - kw + 1
  let g_w := WithLp.equiv 2 _ |>.symm fun
    | Sum.inl (m, n) => ∑ i : Fin h', ∑ j : Fin w',
        (WithLp.equiv 2 _ g_out) (i, j) *
        (WithLp.equiv 2 _ x) (⟨i.val + m.val, by
                                have hi := i.is_lt; have hm := m.is_lt
                                dsimp only [h'] at hi; omega⟩,
                              ⟨j.val + n.val, by
                                have hj := j.is_lt; have hn := n.is_lt
                                dsimp only [w'] at hj; omega⟩)
    | Sum.inr () => ∑ i : Fin h', ∑ j : Fin w', (WithLp.equiv 2 _ g_out) (i, j)
  -- Simplified input gradient for structural purposes
  let g_x := WithLp.equiv 2 _ |>.symm fun _ => 0
  let _ := Wp; let _ := x; -- Avoid unused variable warnings
  (g_w, g_x)

/-- Parameter index type for multi-channel 2D Convolution. -/
abbrev ConvMultiParam (kC kH kW nC : ℕ) := (Fin nC × Fin kC × Fin kH × Fin kW) ⊕ Fin nC

/-- Strided 2D Convolution forward pass with multiple channels. -/
noncomputable def conv2d_strided_forward (nc nh nw nC kh kw s : ℕ)
    (h_h : kh ≤ nh) (h_w : kw ≤ nw) (h_s : 0 < s)
    (Wp : W (ConvMultiParam nc kh kw nC)) (x : W (Fin nc × Fin nh × Fin nw)) :
    W (Fin ((nh - kh) / s + 1) × Fin ((nw - kw) / s + 1) × Fin nC) :=
  let _ := h_s
  let h' := (nh - kh) / s + 1
  let w' := (nw - kw) / s + 1
  WithLp.equiv 2 (Fin h' × Fin w' × Fin nC → ℝ) |>.symm fun (i, j, c_out) =>
    let kernel_sum := ∑ c_in : Fin nc, ∑ m : Fin kh, ∑ n : Fin kw,
      (WithLp.equiv 2 _ Wp) (Sum.inl (c_out, c_in, m, n)) *
      (WithLp.equiv 2 _ x) (c_in,
                            ⟨i.val * s + m.val, by
                              have hi := i.is_lt; have hm := m.is_lt
                              have hi' := Nat.le_of_lt_succ hi
                              have h_b := Nat.div_mul_le_self (nh - kh) s
                              have h_bound := Nat.le_trans (Nat.mul_le_mul_right s hi') h_b
                              omega⟩,
                            ⟨j.val * s + n.val, by
                              have hj := j.is_lt; have hn := n.is_lt
                              have hj' := Nat.le_of_lt_succ hj
                              have h_b := Nat.div_mul_le_self (nw - kw) s
                              have h_bound := Nat.le_trans (Nat.mul_le_mul_right s hj') h_b
                              omega⟩)
    let bias := (WithLp.equiv 2 _ Wp) (Sum.inr c_out)
    kernel_sum + bias

/-- Conv2D Layer instance. -/
noncomputable def conv2d_layer (h w kh kw : ℕ) (h_h : kh ≤ h) (h_w : kw ≤ w) :
    Layer (W (Fin h × Fin w)) (W (Fin (h - kh + 1) × Fin (w - kw + 1))) where
  ParamDim := ConvParam kh kw
  fintypeParamDim := inferInstance
  forward := fun w_p x_p => conv2d_forward h w kh kw h_h h_w w_p x_p
  backward := fun w_p x_p g_p => conv2d_backward h w kh kw h_h h_w w_p x_p g_p

/-- Max Pooling (2x2) forward pass. -/
noncomputable def maxPoolForward (h_dim w_dim : ℕ) (x : W (Fin (2 * h_dim) × Fin (2 * w_dim))) :
    W (Fin h_dim × Fin w_dim) :=
  WithLp.equiv 2 (Fin h_dim × Fin w_dim → ℝ) |>.symm fun p =>
    let (i, j) := p
    let idx_i := 2 * i.val
    let idx_j := 2 * j.val
    let x00 := (WithLp.equiv 2 _ x) (⟨idx_i, by omega⟩, ⟨idx_j, by omega⟩)
    let x01 := (WithLp.equiv 2 _ x) (⟨idx_i, by omega⟩, ⟨idx_j + 1, by omega⟩)
    let x10 := (WithLp.equiv 2 _ x) (⟨idx_i + 1, by omega⟩, ⟨idx_j, by omega⟩)
    let x11 := (WithLp.equiv 2 _ x) (⟨idx_i + 1, by omega⟩, ⟨idx_j + 1, by omega⟩)
    Max.max x00 (Max.max x01 (Max.max x10 x11))

/-- Max Pooling Layer instance. Activation-like (no parameters). -/
noncomputable def maxPoolingLayer (h_dim w_dim : ℕ) :
    Layer (W (Fin (2 * h_dim) × Fin (2 * w_dim))) (W (Fin h_dim × Fin w_dim)) where
  ParamDim := Empty
  fintypeParamDim := inferInstance
  forward := fun _ x => maxPoolForward h_dim w_dim x
  backward := fun _ _ _ => (0, 0) -- Simplified for structural validation

end LeanSharp
