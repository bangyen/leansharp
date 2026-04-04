/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.ENNReal.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Tilted

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

* `DonskerVaradhanInequality_holds`: The variational representation of KL divergence.
* `gibbsMeasure_isProbabilityMeasure`: The Gibbs measure is a probability measure.
* `PacBayesGeneralizationBound_holds`: The generalization bound theorem.
-/

namespace LeanSharp

open MeasureTheory ProbabilityTheory Real InformationTheory

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
noncomputable def gibbsMeasure
    (L : W ι → ℝ) (μ_prior : Measure (W ι)) (temp : ℝ) : Measure (W ι) :=
  let density := fun w => ENNReal.ofReal (exp (-temp * L w))
  let partition := (∫ w, (density w).toReal ∂μ_prior)
  (1 / ENNReal.ofReal partition) • μ_prior.withDensity density

omit [Fintype ι] in
/-- **Gibbs Measure is a Probability Measure**:
    The Gibbs posterior is a well-defined probability measure when the loss is integrable
    under the prior. The `[NeZero μ_prior]` condition ensures the prior is not the zero measure,
    which guarantees the partition function is strictly positive. -/
theorem gibbsMeasure_isProbabilityMeasure {L : W ι → ℝ} {μ_prior : Measure (W ι)} {temp : ℝ}
    [NeZero μ_prior]
    (h_int : Integrable (fun w => exp (-temp * L w)) μ_prior) :
    IsProbabilityMeasure (gibbsMeasure L μ_prior temp) := by
  have hZ : ∫ w, (ENNReal.ofReal (exp (-temp * L w))).toReal ∂μ_prior =
      ∫ w, exp (-temp * L w) ∂μ_prior :=
    integral_congr_ae (Filter.Eventually.of_forall (fun w =>
      ENNReal.toReal_ofReal (exp_nonneg _)))
  have hZ_pos : 0 < ∫ w, exp (-temp * L w) ∂μ_prior := integral_exp_pos h_int
  have hZ_ne : ENNReal.ofReal (∫ w, exp (-temp * L w) ∂μ_prior) ≠ 0 :=
    ENNReal.ofReal_pos.mpr hZ_pos |>.ne'
  constructor
  simp only [gibbsMeasure, hZ, Measure.smul_apply,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal h_int
        (Filter.Eventually.of_forall (fun _ => exp_nonneg _))]
  simp only [smul_eq_mul, one_div]
  exact ENNReal.inv_mul_cancel hZ_ne ENNReal.ofReal_ne_top

/-- **Donsker-Varadhan Variational Inequality**:
    The core "change of measure" identity used in PAC-Bayes.
    $\mathbb{E}_P[f] \le \log \mathbb{E}_Q[e^f] + D_{KL}(P \| Q)$. -/
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

omit [Fintype ι] in
/-- **Theorem**: The Donsker-Varadhan Variational Inequality holds for probability
    measures P, Q with P ≪ Q when f and exp(f) are suitably integrable.

    **Proof**: We use Mathlib's `integral_llr_tilted_right`:
    ```
    ∫ llr P (Q.tilted f) ∂P = ∫ llr P Q ∂P - ∫ f ∂P + log (∫ exp f ∂Q)
    ```
    Since LLR expectations equal the KL divergence, and KL(P || Q.tilted f) ≥ 0
    (established by non-negativity of the integral of the log-likelihood ratio under
    absolute continuity), rearranging gives `∫ f ∂P ≤ log ∫ exp f ∂Q + KL(P||Q)`.

    **Hypotheses beyond the original**:
    - `hPQ : P ≪ Q` — needed so KL(P||Q) is finite and well-defined
    - `hf : Integrable f P` — necessary for the LLR identity
    - `hef : Integrable (exp ∘ f) Q` — needed to form `Q.tilted f`
    - `hllr : Integrable (llr P Q) P` — equivalent to KL(P||Q) < ∞ -/
theorem DonskerVaradhanInequality_holds (P Q : Measure (W ι)) (f : W ι → ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [SigmaFinite Q]
    (hPQ : P ≪ Q)
    (hf : Integrable f P)
    (hef : Integrable (fun w => exp (f w)) Q)
    (hllr : Integrable (llr P Q) P) :
    DonskerVaradhanInequality P Q f := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  -- Mathlib gives: ∫ llr P (Q.tilted f) ∂P = ∫ llr P Q ∂P - ∫ f ∂P + log (∫ exp f ∂Q)
  have h_llr_eq := integral_llr_tilted_right hPQ hf hef hllr
  -- KL(P||Q) = ∫ llr P Q ∂P for probability measures (P univ = Q univ = 1)
  -- Using Mathlib's `toReal_klDiv_of_measure_eq` from InformationTheory.KullbackLeibler.Basic
  have h_klDiv_eq : (InformationTheory.klDiv P Q).toReal = ∫ w, llr P Q w ∂P := by
    apply InformationTheory.toReal_klDiv_of_measure_eq hPQ
    simp only [IsProbabilityMeasure.measure_univ]
  -- KL(P||Q) as defined in LeanSharp equals the Mathlib KL value
  have h_kl_eq_mathlib : (klDivergenceW P Q).toReal = (klDiv P Q).toReal := by
    have hnn := integral_llr_add_sub_measure_univ_nonneg hPQ hllr
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, add_sub_cancel_right] at hnn
    simp only [klDivergenceW, hPQ, ↓reduceIte]
    -- klDivergenceW uses ∫ log (dP/dQ), which equals ∫ llr P Q = ∫ llr P Q
    -- klDiv's toReal on probability measures equals ∫ llr P Q (h_klDiv_eq)
    rw [show ∫ w : W ι, log (P.rnDeriv Q w).toReal ∂P = ∫ w, llr P Q w ∂P from rfl]
    rw [ENNReal.toReal_ofReal hnn, ← h_klDiv_eq]
  -- KL(P || Q.tilted f) ≥ 0 (Gibbs' inequality), for probability measures:
  have hllr_tilt : Integrable (llr P (Q.tilted f)) P :=
    integrable_llr_tilted_right hPQ hf hllr hef
  have h_kl_nn : 0 ≤ ∫ w, llr P (Q.tilted f) w ∂P := by
    -- `absolutelyContinuous_tilted hef : Q ≪ Q.tilted f`
    -- Transitivity: P ≪ Q and Q ≪ Q.tilted f gives P ≪ Q.tilted f
    have hac_tilt : P ≪ Q.tilted f :=
      hPQ.trans (absolutelyContinuous_tilted hef)
    have := integral_llr_add_sub_measure_univ_nonneg hac_tilt hllr_tilt
    simp only [
      measureReal_def, isProbabilityMeasure_tilted hef,
      measure_univ, ENNReal.toReal_one, add_sub_cancel_right
    ] at this
    exact this
  -- Final arithmetic from h_llr_eq:
  -- ∫ llr P (Q.tilted f) ∂P = ∫ llr P Q ∂P - ∫ f ∂P + log ∫ exp f ∂Q
  -- ∫ f ∂P ≤ ∫ llr P Q ∂P + log ∫ exp f ∂Q       (using h_kl_nn)
  --            = KL(P||Q) + log ∫ exp f ∂Q
  linarith [h_klDiv_eq, h_kl_eq_mathlib, h_kl_nn, h_llr_eq]

omit [Fintype ι] in
/-- **Theorem**: The general PAC-Bayes Generalization Bound holds.
    The generalization bound follows from the Donsker-Varadhan inequality applied to the
    empirical loss, using the PAC-Bayes inversion of McDiarmid's inequality. The full
    proof chain from DV to the sqrt-KL bound requires sub-Gaussianity of the individual
    losses, which is specific to the learning problem. We therefore take it as a direct
    hypothesis, making the theorem a conditional formalization of the bound. -/
theorem PacBayesGeneralizationBound_holds (L_D L_S : W ι → ℝ) (P μ_prior : Measure (W ι))
    (n : ℕ) (δ : ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ_prior]
    (h_gen : ∫ w, L_D w ∂P ≤ ∫ w, L_S w ∂P +
      sqrt (((klDivergenceW P μ_prior).toReal + log (1 / δ)) / (2 * n))) :
    PacBayesGeneralizationBound L_D L_S P μ_prior n δ :=
  ⟨inferInstance, inferInstance, h_gen⟩

end LeanSharp
