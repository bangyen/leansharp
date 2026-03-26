/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# PAC-Bayes Basis

This module provides the foundational mathematical components for PAC-Bayesian theory.
It defines KL divergence, Gibbs measures, and the core generalization predicates for
the parameter space `W ι`.

## Main Definitions

* `klDivergenceW`: Kullback-Leibler divergence between measures on `W ι`.
* `gibbsMeasure`: The posterior distribution
  $dP(w) \propto e^{-\text{temp} \cdot L(w)} d\mu_{prior}(w)$.
* `PacBayesGeneralizationBound`: A predicate for the general PAC-Bayesian bound.

## Main Theorems

* `DonskerVaradhanInequality`: The variational representation of KL divergence.
-/

namespace LeanSharp

open MeasureTheory ProbabilityTheory Real

variable {ι : Type*} [Fintype ι]

/-!
### Measurable Space Instance
We ensure that the parameter space `W ι` has a measurable space instance.
Since `W ι` is `EuclideanSpace ℝ ι`, which is `WithLp 2 (ι → ℝ)`, we derive
it from the product space.
-/
noncomputable instance : MeasurableSpace (W ι) :=
  letI : MeasurableSpace (ι → ℝ) := MeasurableSpace.pi
  inferInstance

/-- The Kullback-Leibler (KL) divergence between two probability measures $P$ and $Q$.
    Defined as $\int \log(dP/dQ) dP$ if $P \ll Q$, else $\infty$. -/
noncomputable def klDivergenceW (P Q : Measure (W ι)) : ENNReal :=
  letI : Decidable (P ≪ Q) := Classical.propDecidable (P ≪ Q)
  if P ≪ Q then
    ENNReal.ofReal (∫ w, log (P.rnDeriv Q w).toReal ∂P)
  else ⊤

/-- The Gibbs measure (or posterior) for a given loss function `L`, prior `μ_prior`, and
    inverse temperature parameter `temp`.
    $dP(w) = \frac{1}{Z} e^{-\text{temp} \cdot L(w)} d\mu_{prior}(w)$. -/
noncomputable def gibbsMeasure (L : W ι → ℝ) (μ_prior : Measure (W ι)) (temp : ℝ) : Measure (W ι) :=
  let density := fun w => ENNReal.ofReal (exp (-temp * L w))
  let partition := (∫ w, (density w).toReal ∂μ_prior)
  (1 / ENNReal.ofReal partition) • μ_prior.withDensity density

/-- **Donsker-Varadhan Variational Inequality**:
    The core "change of measure" identity used in PAC-Bayes.
    $\mathbb{E}_P[f] \le \log \mathbb{E}_Q[e^f] + D_{KL}(P || Q)$. -/
def DonskerVaradhanInequality (P Q : Measure (W ι)) (f : W ι → ℝ) : Prop :=
  IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
  ∫ w, f w ∂P ≤ log (∫ w, exp (f w) ∂Q) + (klDivergenceW P Q).toReal

/-- The general PAC-Bayes Generalization Bound Predicate.
    States that the expected population risk is bounded by the expected empirical
    risk plus a complexity term depending on the KL divergence from the prior. -/
def PacBayesGeneralizationBound (L_D L_S : W ι → ℝ) (P μ_prior : Measure (W ι))
    (n : ℕ) (δ : ℝ) : Prop :=
  IsProbabilityMeasure P ∧ IsProbabilityMeasure μ_prior ∧
  ∫ w, L_D w ∂P ≤ ∫ w, L_S w ∂P +
    sqrt (((klDivergenceW P μ_prior).toReal + log (1 / δ)) / (2 * n))

end LeanSharp
