/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.TailFilters

/-!
# Layer-Wise Z-Score Filtering

The paper *Sharpness-Aware Minimization with Z-Score Gradient Filtering*
(arXiv:2505.02369) normalizes each layer separately: for a layer $\ell$ it forms

$$\Omega(g^{(\ell)})_i = (g^{(\ell)}_i - \mu(g^{(\ell)})) / \sigma(g^{(\ell)}),$$

so a coordinate is judged against the statistics of *its own layer* rather than
against the whole parameter vector. `zScoreTailMask` pools every coordinate into
one mean and standard deviation.

This module recovers the paper's semantics by indexing the flat parameter space
with a partition `π : ι → Λ`, whose fibers are the layers. Statistics are taken
fiberwise, and the mask compares each coordinate against its own fiber. No
structural `Chain` machinery is required: the paper's layer-wise normalization is
exactly a partition of the coordinate index.

Taking `π` constant collapses the fibers to a single block and recovers the
global filter, which is the content of `layerTailMask_const` and
`layerTailFilteredGradient_const`.

## Main definitions

* `blockMean`, `blockVariance`, `blockStd`: statistics over one fiber of `π`.
* `layerZScoreTailMask`: the paper's mask, applied fiberwise.
* `layerTailFilteredGradient`: the layer-wise filtered gradient.

## Main theorems

* `norm_sq_layer_tail_filtered_gradient_le`: the filter is an $L_2$ contraction.
* `norm_layer_tail_filtered_gradient_le`: norm-level form of the contraction.
* `fiber_const`: a constant partition has the single fiber `univ`.
* `blockMean_const`: its block mean is the global mean.
* `blockVariance_const`: its block variance is the global variance.
* `blockStd_const`: its block standard deviation is the global one.
* `layerTailMask_const`: a constant partition recovers `zScoreTailMask`.
* `layerTailFilteredGradient_const`: hence it recovers `tailFilteredGradient`.
-/

namespace LeanSharp

open BigOperators

variable {ι : Type*} [Fintype ι] {Λ : Type*} [DecidableEq Λ]

/-- The fiber of the partition `π` containing coordinate index `l`. -/
noncomputable def fiber (π : ι → Λ) (l : Λ) : Finset ι :=
  Finset.univ.filter fun i => π i = l

/-- The mean of `g` over the fiber `π ⁻¹ {l}`. -/
noncomputable def blockMean (g : W ι) (π : ι → Λ) (l : Λ) : ℝ :=
  (∑ i ∈ fiber π l, (WithLp.equiv 2 (ι → ℝ) g) i) / ((fiber π l).card : ℝ)

/-- The variance of `g` over the fiber `π ⁻¹ {l}`. -/
noncomputable def blockVariance (g : W ι) (π : ι → Λ) (l : Λ) : ℝ :=
  (∑ i ∈ fiber π l, ((WithLp.equiv 2 (ι → ℝ) g) i - blockMean g π l)^2)
    / ((fiber π l).card : ℝ)

/-- The standard deviation of `g` over the fiber `π ⁻¹ {l}`. -/
noncomputable def blockStd (g : W ι) (π : ι → Λ) (l : Λ) : ℝ :=
  Real.sqrt (blockVariance g π l)

/-- The paper's Z-score mask applied layer-wise: coordinate `i` is kept exactly when
it is an outlier *within its own fiber* `π i`. -/
noncomputable def layerZScoreTailMask (g : W ι) (π : ι → Λ) (z : ℝ) : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    if |(WithLp.equiv 2 (ι → ℝ) g) i - blockMean g π (π i)| ≤ z * blockStd g π (π i)
      then 0 else 1

/-- The layer-wise filtered gradient: the paper's `∇L(w)_Ω` with per-layer statistics. -/
noncomputable def layerTailFilteredGradient (g : W ι) (π : ι → Λ) (z : ℝ) : W ι :=
  hadamard g (layerZScoreTailMask g π z)

/-- **Layer-Wise Contraction**: filtering fiberwise never increases the squared norm.
As for the global filters, this holds because the mask is `0`/`1`-valued. -/
theorem norm_sq_layer_tail_filtered_gradient_le (g : W ι) (π : ι → Λ) (z : ℝ) :
    ‖layerTailFilteredGradient g π z‖^2 ≤ ‖g‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  unfold layerTailFilteredGradient hadamard layerZScoreTailMask
  rw [WithLp.equiv_apply, Equiv.apply_symm_apply]
  dsimp only [ge_iff_le, WithLp.equiv_symm_apply, Real.norm_eq_abs]
  split_ifs
  · simp only [
      mul_zero,
      ne_eq,
      OfNat.ofNat_ne_zero,
      not_false_eq_true,
      zero_pow,
      sq_abs
    ]
    positivity
  · rw [mul_one, sq_abs]

/-- **Layer-Wise Filtered Norm Bound**: norm-level form of the contraction. -/
theorem norm_layer_tail_filtered_gradient_le (g : W ι) (π : ι → Λ) (z : ℝ) :
    ‖layerTailFilteredGradient g π z‖ ≤ ‖g‖ := by
  have h_sq := norm_sq_layer_tail_filtered_gradient_le g π z
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  exact h_sqrt

/-- A constant partition has a single fiber, namely all of `ι`. -/
lemma fiber_const (l₀ : Λ) : fiber (fun _ : ι => l₀) l₀ = Finset.univ := by
  unfold fiber
  simp only [Finset.filter_eq_self, implies_true]

/-- Over a constant partition the block mean is the global mean. -/
lemma blockMean_const (g : W ι) (l₀ : Λ) :
    blockMean g (fun _ : ι => l₀) l₀ = vectorMean g := by
  unfold blockMean vectorMean
  rw [fiber_const, Finset.card_univ]

/-- Over a constant partition the block variance is the global variance. -/
lemma blockVariance_const (g : W ι) (l₀ : Λ) :
    blockVariance g (fun _ : ι => l₀) l₀ = vectorVariance g := by
  unfold blockVariance vectorVariance
  rw [blockMean_const, fiber_const, Finset.card_univ]

/-- Over a constant partition the block standard deviation is the global one. -/
lemma blockStd_const (g : W ι) (l₀ : Λ) :
    blockStd g (fun _ : ι => l₀) l₀ = vectorStd g := by
  unfold blockStd vectorStd
  rw [blockVariance_const]

/-- **Reduction to the global mask**: a single-layer network — a constant partition —
recovers `zScoreTailMask` exactly. -/
theorem layerTailMask_const (g : W ι) (z : ℝ) (l₀ : Λ) :
    layerZScoreTailMask g (fun _ : ι => l₀) z = zScoreTailMask g z := by
  apply (WithLp.equiv 2 (ι → ℝ)).injective
  ext i
  unfold layerZScoreTailMask zScoreTailMask
  simp only [Equiv.apply_symm_apply, blockMean_const, blockStd_const]

/-- **Reduction to the global filter**: hence a constant partition recovers
`tailFilteredGradient`. -/
theorem layerTailFilteredGradient_const (g : W ι) (z : ℝ) (l₀ : Λ) :
    layerTailFilteredGradient g (fun _ : ι => l₀) z = tailFilteredGradient g z := by
  unfold layerTailFilteredGradient tailFilteredGradient
  rw [layerTailMask_const]

end LeanSharp
