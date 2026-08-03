/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Layers.Architectures.Attention
import Mathlib.GroupTheory.Perm.Basic

/-!
# Attention Permutation Equivariance

This module formalizes the permutation equivariance of the scaled dot-product
attention mechanism. The core property is that permuting the sequence positions
of inputs commutes with the attention forward pass.

## Main Definitions

* `permuteSeq`: Permutes the sequence dimension of a `W (Fin S × Fin D)` tensor.

## Main Theorems

* `permuteSeq_apply`: The coordinate of a permuted sequence is the reindexed original.
* `softmax_perm`: Permuting the input to softmax permutes the output.
* `attention_permutation_equivariance`: Permuting Q, K, V by σ before attention
  produces the same result as applying σ to the attention output.
* `attention_output_sum_invariant`: The sum over rows is invariant under permutation.
* `sum_perm_eq`: Inner products of rows are reindexed by the permutation.
-/

namespace LeanSharp

open Finset BigOperators Real

variable {S D : ℕ} [NeZero S] [NeZero D]

/-- Permute the sequence dimension of a `W (Fin S × Fin D)` tensor by `σ`.
    This reindexes the rows of the sequence while keeping feature dims fixed. -/
noncomputable def permuteSeq (σ : Equiv.Perm (Fin S)) (x : W (Fin S × Fin D)) :
    W (Fin S × Fin D) :=
  (WithLp.equiv 2 _).symm fun (i, d) => (WithLp.equiv 2 _ x) (σ.symm i, d)

omit [NeZero S] [NeZero D] in
/-- Unfolding lemma: coordinate of `permuteSeq σ x` at `(i, d)`. -/
lemma permuteSeq_apply (σ : Equiv.Perm (Fin S)) (x : W (Fin S × Fin D))
    (i : Fin S) (d : Fin D) :
    (WithLp.equiv 2 _ (permuteSeq σ x)) (i, d) = (WithLp.equiv 2 _ x) (σ.symm i, d) := by
  simp only [permuteSeq, WithLp.equiv_symm_apply, WithLp.equiv_apply]

omit [NeZero S] in
/-- Inner product of two rows after permutation: the row sums are reindexed by σ. -/
lemma sum_perm_eq (σ : Equiv.Perm (Fin S)) (f : Fin S → ℝ) :
    ∑ j : Fin S, f (σ j) = ∑ j : Fin S, f j :=
  Equiv.sum_comp σ f

/-- **Softmax Permutation Equivariance**:
    Permuting the input to softmax by σ permutes the output by σ.
    This holds because the denominator (partition function) is a sum over all indices
    and is thus invariant under the permutation. -/
lemma softmax_perm [Fintype ι] (σ : Equiv.Perm ι) (x : W ι) :
    softmax ((WithLp.equiv 2 _).symm fun i => (WithLp.equiv 2 _ x) (σ i)) =
    (WithLp.equiv 2 _).symm fun i => (WithLp.equiv 2 _ (softmax x)) (σ i) := by
  ext i
  simp only [softmax, WithLp.equiv_symm_apply, WithLp.equiv_apply]
  congr 1
  -- The denominator ∑ j, exp(x_{σ j}) = ∑ j, exp(x_j) by reindexing
  exact Equiv.sum_comp σ (fun j => Real.exp (x.ofLp j))

omit [NeZero S] [NeZero D] in
/-- **Attention Permutation Equivariance**:
    Permuting the sequence dimension of Q, K, V commutes with `attentionForward`.
    That is, `attentionForward (permuteSeq σ Q) (permuteSeq σ K) (permuteSeq σ V)`
    equals `permuteSeq σ (attentionForward Q K V)`. -/
theorem attention_permutation_equivariance
    (σ : Equiv.Perm (Fin S)) (Q K V : W (Fin S × Fin D)) :
    attentionForward S D (permuteSeq σ Q) (permuteSeq σ K) (permuteSeq σ V) =
    permuteSeq σ (attentionForward S D Q K V) := by
  ext ⟨i, d⟩
  simp only [attentionForward, permuteSeq, WithLp.equiv_symm_apply, WithLp.equiv_apply, softmax]
  -- Denominator equality: ∑ j', exp(A[σ⁻¹ i, σ⁻¹ j']) = ∑ j', exp(A[σ⁻¹ i, j'])
  have h_denom : ∑ j' : Fin S,
        Real.exp ((∑ k, Q.ofLp (σ.symm i, k) * K.ofLp (σ.symm j', k)) / Real.sqrt D) =
      ∑ j' : Fin S,
        Real.exp ((∑ k, Q.ofLp (σ.symm i, k) * K.ofLp (j', k)) / Real.sqrt D) :=
    Equiv.sum_comp σ.symm fun j' =>
      Real.exp ((∑ k, Q.ofLp (σ.symm i, k) * K.ofLp (j', k)) / Real.sqrt D)
  -- The full LHS sum equals the RHS by reindexing j → σ.symm j on the outer sum
  -- and using h_denom to equate the denominators
  apply Finset.sum_nbij (fun j => σ.symm j) (by simp only [Finset.mem_univ, implies_true]) (by
    intro a _ b _ hab
    exact σ.symm.injective hab)
    (by intro b _; exact ⟨σ b, Finset.mem_coe.mpr (Finset.mem_univ _), σ.symm_apply_apply b⟩)
  intro j _
  rw [h_denom]

omit [NeZero S] [NeZero D] in
/-- **Corollary**: The total sum over all sequence positions is invariant under permutation. -/
theorem attention_output_sum_invariant
    (σ : Equiv.Perm (Fin S)) (Q K V : W (Fin S × Fin D)) (d : Fin D) :
    ∑ i : Fin S, (WithLp.equiv 2 _ (attentionForward S D
        (permuteSeq σ Q) (permuteSeq σ K) (permuteSeq σ V))) (i, d) =
    ∑ i : Fin S, (WithLp.equiv 2 _ (attentionForward S D Q K V)) (i, d) := by
  rw [attention_permutation_equivariance]
  simp only [permuteSeq, WithLp.equiv_symm_apply, WithLp.equiv_apply]
  exact sum_perm_eq σ.symm fun i =>
    (WithLp.equiv 2 _ (attentionForward S D Q K V)) (i, d)

end LeanSharp
