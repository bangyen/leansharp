/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Layers.Basic.Activation
import LeanSharp.Layers.Basic.Dropout
import LeanSharp.Layers.Basic.Linear

/-!
# Basic Layer Tests

This module verifies elemental feedforward layers: Linear, ReLU, Softmax, and Dropout.

## Examples
-/

namespace LeanSharp.Tests

/-- Test: ReLU non-negativity. -/
example (x : W (Fin 10)) :
    ∀ i, (WithLp.equiv 2 _ (relu x)) i ≥ 0 := by
  unfold relu
  intro i
  exact le_max_left (0 : ℝ) ((WithLp.equiv 2 _ x) i)

/-- Test: Linear Layer Parameter Dimensions. -/
example (M N : ℕ) [Fintype (Fin M)] [Fintype (Fin N)] :
    (linearLayer (Fin M) (Fin N)).ParamDim = ((Fin N × Fin M) ⊕ Fin N) :=
  rfl

/-- Test: Linear Layer forward pass with zero weights and bias is zero. -/
example {M N : ℕ} (x : W (Fin M)) :
    (linearLayer (Fin M) (Fin N)).forward 0 x = 0 := by
  unfold linearLayer linearForward
  ext i
  simp only [
    WithLp.equiv_apply,
    PiLp.zero_apply,
    zero_mul,
    add_zero,
    Finset.sum_const_zero,
    WithLp.equiv_symm_apply
  ]

/-- Test: Dropout forward pass with mask of ones and p=0 is identity. -/
example {ι : Type} [Fintype ι] (x : W ι) :
    dropoutForward 0 (WithLp.equiv 2 _ |>.symm fun _ => 1) x = x := by
  unfold dropoutForward
  ext i
  simp only [sub_zero, div_one, mul_one, WithLp.equiv_apply, WithLp.equiv_symm_apply]

/-- Test: Softmax output sums to 1. -/
example {ι : Type} [Fintype ι] [Nonempty ι] (x : W ι) :
    ∑ i, (WithLp.equiv 2 _ (softmax x)) i = 1 := by
  unfold softmax
  simp only [WithLp.equiv_apply, WithLp.equiv_symm_apply]
  rw [← Finset.sum_div]
  apply div_self
  apply ne_of_gt
  apply Finset.sum_pos
  · intros i _
    apply Real.exp_pos
  · apply Finset.univ_nonempty

/-- Test: Softmax non-negativity. -/
example {ι : Type} [Fintype ι] [Nonempty ι] (x : W ι) :
    ∀ i, (WithLp.equiv 2 _ (softmax x)) i > 0 := by
  unfold softmax
  intro i
  simp only [WithLp.equiv_apply, WithLp.equiv_symm_apply]
  apply div_pos
  · apply Real.exp_pos
  · apply Finset.sum_pos
    · intros j _
      apply Real.exp_pos
    · exact Finset.univ_nonempty

end LeanSharp.Tests
