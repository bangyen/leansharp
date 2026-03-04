import LeanSharp.Landscape
import Mathlib.Data.Finset.Sum

/-!
# Stochastics & Empirical Risk

In standard Machine Learning, we don't optimize the true population risk
$L_\mathcal{D}(w)$ directly. Instead, we optimize the empirical risk
$L_\mathcal{S}(w) = \frac{1}{n} \sum_{i=1}^n \ell(w; x_i, y_i)$ over a dataset $\mathcal{S}$.

This file formally defines datasets, data points, and the empirical risk operator.
-/

variable {d : ℕ}

-- A generic data point type. It could represent `(x, y)` pairs or just inputs.
variable (DataPoint : Type*)

-- The per-sample loss function `ℓ`.
-- Given parameter weights `w` and a single `DataPoint`, it returns a Real loss.
variable (sample_loss : W d → DataPoint → ℝ)

-- A dataset `S` is formally represented as an array (or list/finset) of `DataPoint`s. 
-- Here, we use a function from `Fin n → DataPoint` to represent a 
-- fixed-size dataset of `n` items.
variable {n : ℕ} (S : Fin n → DataPoint)

/-- The number of samples `n` cast to a Real number for averages. -/
noncomputable def n_real (n : ℕ) : ℝ := (n : ℝ)

/-- The empirical risk (loss) over the entire dataset `S` given parameters `w`.
    $L_S(w) = \frac{1}{n} \sum_{i=1}^n \ell(w; S[i])$ -/
noncomputable def empirical_risk (w : W d) : ℝ :=
  if n = 0 then 0 else 
  (∑ i : Fin n, sample_loss w (S i)) / n_real n

/-!
## Stochastic Minibatches

During SAM/ZSharp training, we take gradient steps based on random
minibatches, not the fully empirical risk.
-/

-- A minibatch `B` is simply a subset of indices of the dataset `S`.
variable {b : ℕ} (B : Fin b → Fin n)

/-- The minibatch loss function over subset `B`. -/
noncomputable def minibatch_risk (w : W d) : ℝ :=
  if b = 0 then 0 else 
  (∑ i : Fin b, sample_loss w (S (B i))) / n_real b
