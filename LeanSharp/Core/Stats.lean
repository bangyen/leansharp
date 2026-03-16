/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Sam
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Bounded

namespace LeanSharp

open BigOperators

variable {ι : Type*} [Fintype ι]

/-- The mean of a vector in `W = ℝ^d`. -/
noncomputable def vector_mean (g : W ι) : ℝ :=
  (∑ i : ι, (WithLp.equiv 2 (ι → ℝ) g) i) / (Fintype.card ι : ℝ)

/-- The variance of a vector in $W = ℝ^d$. -/
noncomputable def vector_variance (g : W ι) : ℝ :=
  let μ := vector_mean g
  (∑ i : ι, ((WithLp.equiv 2 (ι → ℝ) g) i - μ)^2) / (Fintype.card ι : ℝ)

/-- The standard deviation `σ` is the square root of the variance. -/
noncomputable def vector_std (g : W ι) : ℝ :=
  Real.sqrt (vector_variance g)

/-- The mean of a scalar-multiple vector is the scalar multiple of the original mean. -/
@[simp]
lemma vector_mean_smul (k : ℝ) (g : W ι) :
    vector_mean (k • g) = k * vector_mean g := by
  unfold vector_mean
  have h_smul (i : ι) :
    (WithLp.equiv 2 (ι → ℝ) (k • g)) i = k * (WithLp.equiv 2 (ι → ℝ) g) i := rfl
  simp only [h_smul, ← Finset.mul_sum]
  rw [mul_div_assoc]

/-- The standard deviation scales linearly with a non-negative scalar. -/
@[simp]
lemma vector_std_smul {k : ℝ} (hk : 0 ≤ k) (g : W ι) :
    vector_std (k • g) = k * vector_std g := by
  unfold vector_std
  have h_var_smul : vector_variance (k • g) = k^2 * vector_variance g := by
    unfold vector_variance; rw [vector_mean_smul]
    have h_inner (i : ι) : ((WithLp.equiv 2 (ι → ℝ) (k • g)) i - k * vector_mean g)^2 =
      k^2 * ((WithLp.equiv 2 (ι → ℝ) g) i - vector_mean g)^2 := by
      have : (WithLp.equiv 2 (ι → ℝ) (k • g)) i = k * (WithLp.equiv 2 (ι → ℝ) g) i := rfl
      rw [this, ← mul_sub, mul_pow]
    simp only [h_inner, ← Finset.mul_sum, mul_div_assoc]
  rw [h_var_smul]
  have h_nonneg : 0 ≤ vector_variance g := by
    unfold vector_variance
    positivity
  rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk]

/-- The sum of Euclidean distances from `m` to a set of vectors `g_i` is continuous. -/
lemma continuous_sum_distances {α : Type*} (s : Finset α) (g : α → W ι) :
    Continuous (fun m : W ι => ∑ i ∈ s, ‖g i - m‖) := by
  apply continuous_finset_sum
  intro i _
  apply continuous_norm.comp
  apply continuous_const.sub continuous_id

/-- The sum of distances is coercive: it tends to infinity as `m` grows. -/
lemma tendsto_sum_distances_cocompact {α : Type*} (s : Finset α) (g : α → W ι) (hs : s.Nonempty) :
    Filter.Tendsto (fun m : W ι => ∑ i ∈ s, ‖g i - m‖) (Filter.cocompact (W ι)) Filter.atTop := by
  let i0 := hs.choose
  have hi0 : i0 ∈ s := hs.choose_spec
  apply Filter.tendsto_atTop_mono (α := W ι) (f := fun m => ‖g i0 - m‖)
  · intro m
    apply Finset.single_le_sum (f := fun i => ‖g i - m‖) (fun i _ => norm_nonneg _) hi0
  · -- tendsto ‖g i0 - m‖ cocompact implies it grows.
    apply Filter.tendsto_atTop_mono (f := fun m => ‖m‖ - ‖g i0‖)
    · intro m; rw [norm_sub_rev]; apply norm_sub_norm_le
    · rw [Filter.tendsto_atTop]
      intro b
      filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (b + ‖g i0‖)] with m hm
      linarith

/-- The geometric median exists for any finite set of points in a finite-dim space. -/
lemma exists_isMin_on_finite_sum_norm {α : Type*} (s : Finset α) (g : α → W ι) (hs : s.Nonempty) :
    ∃ m : W ι, IsMinOn (fun m => ∑ i ∈ s, ‖g i - m‖) Set.univ m := by
  let f := fun m : W ι => ∑ i ∈ s, ‖g i - m‖
  have hf : Continuous f := continuous_sum_distances s g
  have h_coercive := tendsto_sum_distances_cocompact s g hs
  let m0 : W ι := g hs.choose
  have hev : ∀ᶠ (x : W ι) in Filter.cocompact (W ι), f m0 ≤ f x :=
    h_coercive.eventually (Filter.eventually_ge_atTop (f m0))
  have ⟨m, hm⟩ := hf.exists_forall_le' m0 hev
  exact ⟨m, fun x _ => hm x⟩

/-- The Multivariate (Geometric) Median minimizes the sum of Euclidean distances. -/
noncomputable def geometric_median {α : Type*} (s : Finset α) (g : α → W ι) : W ι :=
  if h : s.Nonempty then
    Classical.choose (exists_isMin_on_finite_sum_norm s g h)
  else
    0

/-- When `s` is nonempty, `geometric_median` equals the chosen minimizer; used to apply
`Classical.choose_spec` in robustness proofs. -/
lemma geometric_median_eq_choose {α : Type*} (s : Finset α) (g : α → W ι) (h : s.Nonempty) :
    geometric_median s g = Classical.choose (exists_isMin_on_finite_sum_norm s g h) := by
  unfold geometric_median; rw [dif_pos h]

end LeanSharp
