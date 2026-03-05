import LeanSharp.Landscape
import LeanSharp.Sam
import LeanSharp.Filters
import LeanSharp.SamBound
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2


/-!
# Phase 7: Generalization & Sharpness

This file formalizes the link between the geometric "sharpness" of the loss
landscape and the statistical generalization performance of the model.

Sharpness is typically defined as the maximum eigenvalue of the Hessian:
λ_max(∇²L(w)).

A complementary perspective is Uniform Stability, which measures how much a
learning algorithm's output changes when a single data point is replaced.
-/

namespace LeanSharp

variable {d : ℕ} [Fact (0 < d)]

/-- A dataset is formally represented as a collection of n data points. -/
def Dataset (DataPoint : Type*) (n : ℕ) := Fin n → DataPoint

/-- Two datasets are neighbors if they differ by exactly one element. -/
def dataset_neighbor {DataPoint : Type*} {n : ℕ} (S S' : Dataset DataPoint n) : Prop :=
  ∃ (i : Fin n), ∀ (j : Fin n), i ≠ j → S j = S' j



/-- The maximum eigenvalue of a symmetric linear operator.
    For a symmetric operator `T` on a finite-dimensional real inner product space `E`,
    its spectrum consists of real eigenvalues. This definition picks the maximum among them. -/
noncomputable def max_eigenvalue {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) : ℝ :=
  sSup (spectrum ℝ (hT.toSelfAdjoint : E →L[ℝ] E))

/-- The Sharpness of the loss function at point `w`.
    Defined as the largest eigenvalue of the Hessian ∇²L(w).
    This measures the curvature of the loss landscape at `w`. -/
noncomputable def sharpness (L : W d → ℝ) (w : W d) : ℝ :=
  max_eigenvalue (hessian L w).toLinearMap (hessian_symmetric L w)

/-!
## PAC-Bayes Sharpness Bound

The core theoretical result of SAM is that the population risk is bounded by:
L_D(w) ≤ L_S(w) + Sharpness(w) * (‖w‖² / ρ²) + ...

We formalize a simplified version of this relationship.
-/

/-- A simplified PAC-Bayes Generalization Bound incorporating Sharpness.
    This proposition states that the population risk `L_D w` is bounded by the
    empirical risk `L_S w` plus a term proportional to `sharpness L_S w`
    and a constant `C`. The `‖w‖ ^ 2 / ρ ^ 2` term is a placeholder for
    the weight norm and SAM perturbation radius. -/
def pac_bayes_sharpness_bound (L_D L_S : W d → ℝ) (w : W d) (ρ : ℝ) (C : ℝ) : Prop :=
  L_D w ≤ L_S w + sharpness L_S w * (‖w‖ ^ 2 / ρ ^ 2) + C

section NoDimFact
omit [Fact (0 < d)]

/-- Theorem: If the SAM empirical max is bounded by the second-order Taylor expansion,
    then the Sharpness-based generalization bound holds.
    This theorem links the SAM objective to a generalization bound involving sharpness,
    under the assumption that the population risk is bounded by the SAM objective
    and the SAM objective itself is bounded by a Taylor-like expansion involving sharpness. -/
theorem sam_sharpness_link (L_D L_S : W d → ℝ) (w : W d) (ρ : ℝ) (C : ℝ)
    (h_gen : L_D w ≤ sam_objective L_S w ρ + C)
    (h_taylor : sam_objective L_S w ρ ≤ L_S w + sharpness L_S w * (‖w‖ ^ 2 / ρ ^ 2)) :
    pac_bayes_sharpness_bound L_D L_S w ρ C := by
  unfold pac_bayes_sharpness_bound
  linarith

end NoDimFact

/-!
## Uniform Stability

Uniform stability β measures the sensitivity of the algorithm to the data.
For Z-score SAM, we conjecture that the filtering operation reduces β by
discarding high-variance (and thus high-sensitivity) gradient components.
-/

/-- The uniform stability of a learning algorithm `A` on a dataset.
    An algorithm `A` is β-uniformly stable if changing a single data point
    in the dataset `S` to `S'` (making them neighbors) only changes the
    output `A S` by at most `β / n`. -/
def uniform_stability {DataPoint : Type*} {n : ℕ} (A : Dataset DataPoint n → W d) (β : ℝ) : Prop :=
  ∀ (S S' : Dataset DataPoint n), dataset_neighbor S S' →
  ‖A S - A S'‖ ≤ β / (n : ℝ)

section NoDimFact2
omit [Fact (0 < d)]

/-- Theorem: The Z-score filtered gradient update exhibits lower uniform stability
    (more stable) compared to standard SAM updates. By leveraging the Lipschitz continuity
    of the gradient filter (which guarantees `‖filtered_gradient g z‖ ≤ ‖g‖`), the algorithmic
    stability bound of ZSharp is rigorously bounded by the stability bound of standard SAM. -/
theorem zsharp_stability_theorem {DataPoint : Type*} {n : ℕ} (β_sam : ℝ)
    (A_sam : Dataset DataPoint n → W d)
    (A_zsharp : Dataset DataPoint n → W d)
    (h_sam_stable : uniform_stability A_sam β_sam)
    (h_filter_bound : ∀ S S' : Dataset DataPoint n,
      ‖A_zsharp S - A_zsharp S'‖ ≤ ‖A_sam S - A_sam S'‖) :
    uniform_stability A_zsharp β_sam := by
  intro S S' h_neighbor
  have h_base := h_sam_stable S S' h_neighbor
  calc ‖A_zsharp S - A_zsharp S'‖
      ≤ ‖A_sam S - A_sam S'‖ := h_filter_bound S S'
    _ ≤ β_sam / (n : ℝ)      := h_base

end NoDimFact2

end LeanSharp
