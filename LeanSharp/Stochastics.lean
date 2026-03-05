import LeanSharp.Landscape
import LeanSharp.Sam
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Set.Basic

set_option linter.style.longLine false

/-!
# Stochastics & Empirical Risk

In standard Machine Learning, we don't optimize the true population risk
$L_\mathcal{D}(w)$ directly. Instead, we optimize the empirical risk
$L_\mathcal{S}(w) = \frac{1}{n} \sum_{i=1}^n \ell(w; x_i, y_i)$ over a dataset $\mathcal{S}$.

This file formally defines datasets, data points, and the empirical risk operator.
-/

namespace LeanSharp

open BigOperators

variable {d : ℕ} [Fact (0 < d)]

/-- A dataset is formally represented as a collection of n data points. -/
def Dataset (DataPoint : Type*) (n : ℕ) := Fin n → DataPoint

/-- Two datasets are neighbors if they differ by exactly one element. -/
def dataset_neighbor {DataPoint : Type*} {n : ℕ} (S S' : Dataset DataPoint n) : Prop :=
  ∃ (i : Fin n), ∀ (j : Fin n), i ≠ j → S j = S' j

/-- The number of samples `n` cast to a Real number for averages. -/
noncomputable def n_real (n : ℕ) : ℝ := (n : ℝ)

/-- The empirical risk (loss) over the entire dataset `S` given parameters `w`.
    $L_S(w) = \frac{1}{n} \sum_{i=1}^n \ell(w; S[i])$ -/
noncomputable def empirical_risk {DataPoint : Type*} (sample_loss : W d → DataPoint → ℝ)
    {n : ℕ} (S : Dataset DataPoint n) (w : W d) : ℝ :=
  if n = 0 then 0 else
  (∑ i : Fin n, sample_loss w (S i)) / n_real n

/-- The minibatch loss function over subset `B`. -/
noncomputable def minibatch_risk {DataPoint : Type*} (sample_loss : W d → DataPoint → ℝ)
    {n : ℕ} (S : Dataset DataPoint n) {b : ℕ} (B : Fin b → Fin n) (w : W d) : ℝ :=
  if b = 0 then 0 else
  (∑ i : Fin b, sample_loss w (S (B i))) / n_real b

/-- The full gradient (full batch) over the entire dataset. -/
noncomputable def full_gradient {DataPoint : Type*} (sample_loss : W d → DataPoint → ℝ)
    {n : ℕ} (S : Dataset DataPoint n) (w : W d) : W d :=
  gradient (empirical_risk sample_loss S) w

/-- The minibatch gradient (stochastic gradient). -/
noncomputable def minibatch_gradient {DataPoint : Type*} (sample_loss : W d → DataPoint → ℝ)
    {n : ℕ} (S : Dataset DataPoint n) {b : ℕ} (B : Fin b → Fin n) (w : W d) : W d :=
  gradient (minibatch_risk sample_loss S B) w

/-- The stochastic error (noise) at a given point `w` for minibatch `B`. -/
noncomputable def stochastic_error {DataPoint : Type*} (sample_loss : W d → DataPoint → ℝ)
    {n : ℕ} (S : Dataset DataPoint n) {b : ℕ} (B : Fin b → Fin n) (w : W d) : W d :=
  minibatch_gradient sample_loss S B w - full_gradient sample_loss S w

/-- A property for a collection of minibatches being unbiased. -/
def is_unbiased {DataPoint : Type*} (sample_loss : W d → DataPoint → ℝ)
    {n : ℕ} (S : Dataset DataPoint n) {b : ℕ} (w : W d) (batches : Set (Fin b → Fin n)) : Prop :=
  sorry

/-- The bounded variance assumption: the expected squared norm of the
    stochastic error is bounded by some constant σ². -/
def has_bounded_variance {DataPoint : Type*} (sample_loss : W d → DataPoint → ℝ)
    {n : ℕ} (S : Dataset DataPoint n) {b : ℕ} (w : W d) (batches : Set (Fin b → Fin n)) (σ : ℝ) : Prop :=
  ∀ B ∈ batches, ‖stochastic_error sample_loss S B w‖^2 ≤ σ^2

end LeanSharp
