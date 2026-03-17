/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Layers.Architectures.ViT
import LeanSharp.Layers.Specialized.Convolution
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

namespace LeanSharp

open BigOperators

/-- **ViT Patching Invariance**:
    The Patch Embedding layer is mathematically equivalent to a 2D convolution
    where the kernel size and stride both equal the patch size. -/
theorem patch_embedding_eq_strided_conv (nc nh nw np ns nd : ℕ)
    [NeZero nh] [NeZero nw] [NeZero np] [NeZero ns]
    (h_patch_size : ns = (nh / np) * (nw / np))
    (h_nh_div : np ∣ nh) (h_nw_div : np ∣ nw) :
    ∀ (w : W ((Fin nc × Fin np × Fin np) × Fin nd))
      (x : W (Fin nc × Fin nh × Fin nw)),
    (patch_embedding nc nh nw np ns nd).forward w x =
    let w_conv : W (ConvMultiParam nc np np nd) :=
      WithLp.equiv 2 _ |>.symm fun
        | Sum.inl (d, c, ph, pw) => (WithLp.equiv 2 _ w) ((c, ph, pw), d)
        | Sum.inr _ => 0
    let h_nh_le := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne nh)) h_nh_div
    let h_nw_le := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne nw)) h_nw_div
    let h_pos : 0 < np := NeZero.pos np
    let h_nh_pos : 0 < nh / np := Nat.div_pos h_nh_le h_pos
    let h_nw_pos : 0 < nw / np := Nat.div_pos h_nw_le h_pos
    have h_h' : (nh - np) / np + 1 = nh / np := by
      have h1 : nh / np * np = nh := Nat.div_mul_cancel h_nh_div
      have h2 : (nh / np - 1) * np = nh - np := by
        rw [Nat.mul_sub_right_distrib, h1, Nat.one_mul]
      rw [← h2, Nat.mul_div_cancel _ h_pos]
      exact Nat.sub_add_cancel h_nh_pos
    have h_w' : (nw - np) / np + 1 = nw / np := by
      have h1 : nw / np * np = nw := Nat.div_mul_cancel h_nw_div
      have h2 : (nw / np - 1) * np = nw - np := by
        rw [Nat.mul_sub_right_distrib, h1, Nat.one_mul]
      rw [← h2, Nat.mul_div_cancel _ h_pos]
      exact Nat.sub_add_cancel h_nw_pos
    let out_conv := conv2d_strided_forward nc nh nw nd np np np
      h_nh_le h_nw_le h_pos w_conv x
    WithLp.equiv 2 _ |>.symm fun (s, d) =>
      let i_idx : ℕ := (s : ℕ) / (nw / np)
      let j_idx : ℕ := (s : ℕ) % (nw / np)
      have h_i : i_idx < (nh - np) / np + 1 := by
        rw [h_h']
        apply Nat.div_lt_of_lt_mul
        rw [Nat.mul_comm, ← h_patch_size]
        exact s.is_lt
      have h_j : j_idx < (nw - np) / np + 1 := by
        rw [h_w']
        exact Nat.mod_lt _ h_nw_pos
      (WithLp.equiv 2 _ out_conv) (⟨i_idx, h_i⟩, ⟨j_idx, h_j⟩, d) := by
  intro w x
  apply (WithLp.equiv 2 (Fin ns × Fin nd → ℝ)).injective
  ext p
  obtain ⟨s, d⟩ := p
  simp only [WithLp.equiv_symm_apply, WithLp.equiv_apply]
  unfold patch_embedding conv2d_strided_forward
  dsimp only [Layer.forward]
  simp only [WithLp.equiv_symm_apply, WithLp.equiv_apply]
  rw [add_zero]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro ph _
  apply Finset.sum_congr rfl
  intro pw _
  simp only [mul_comm]
  congr 1
  -- Weight match is solved by congr 1, only input index match remains
  apply congr_arg
  let i_val := ↑s / (nw / np)
  let j_val := ↑s % (nw / np)
  apply Prod.ext
  · rfl -- c
  · apply Prod.ext
    · -- h index
      apply Fin.ext
      dsimp only [Fin.val_ofNat]
      rw [Fin.val_mk]
      have h_max_s : (s : ℕ) < (nh / np) * (nw / np) := by rw [← h_patch_size]; exact s.is_lt
      have h_max_i : i_val < nh / np := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h_max_s)
      have h_bound : np * i_val + ↑ph < nh := by
        calc np * i_val + ↑ph < (i_val + 1) * np := by rw [Nat.mul_comm]; linarith [ph.is_lt]
          _ ≤ (nh / np) * np := Nat.mul_le_mul_right np h_max_i
          _ = nh := Nat.div_mul_cancel h_nh_div
      rw [Nat.mod_eq_of_lt h_bound, Nat.mul_comm]
    · -- w index
      apply Fin.ext
      dsimp only [Fin.val_ofNat]
      rw [Fin.val_mk]
      have h_pos : 0 < np := NeZero.pos np
      have h_nw_pos : 0 < nw / np :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne nw)) h_nw_div) h_pos
      have h_max_j : j_val < nw / np := Nat.mod_lt (s : ℕ) h_nw_pos
      have h_bound : np * j_val + ↑pw < nw := by
        calc np * j_val + ↑pw < (j_val + 1) * np := by rw [Nat.mul_comm]; linarith [pw.is_lt]
          _ ≤ (nw / np) * np := Nat.mul_le_mul_right np h_max_j
          _ = nw := Nat.div_mul_cancel h_nw_div
      rw [Nat.mod_eq_of_lt h_bound, Nat.mul_comm]

end LeanSharp
