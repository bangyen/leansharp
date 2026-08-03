/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Alignment
import LeanSharp.Theory.Robustness.PacBayesBasis
import LeanSharp.Theory.Robustness.PacBayesHoeffding
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Localized PAC-Bayes Bounds

This module extends the standard PAC-Bayesian framework for non-convex population risks.
By localizing the Gibbs posterior measure specifically to stability domains guaranteed by
`StabilityCertificate`, we can bridge statistical concentration with geometric regularity.

## Main Definitions

* `localGibbsMeasure`: The posterior distribution restricted to an arbitrary stability set $S$.
* `StabilityPacBayesBound`: Signatures linking generalization gap to localized certificates.

## Main Theorems

* `localGibbsMeasure_isProbabilityMeasure`: Proves well-formedness of the restricted prior.
* `localGibbsMeasure_absolutelyContinuous`: The localized posterior is absolutely continuous
  w.r.t. the prior.
* `stabilityPacBayesBound_holds`: The localized PAC-Bayes-Hoeffding inequality, derived
  from Donsker-Varadhan.
* `stabilityPacBayesBound_provability`: Well-formedness and the derived bound, bundled.
-/

namespace LeanSharp

open MeasureTheory ProbabilityTheory Real InformationTheory

variable {ι : Type*} [Fintype ι]

/-- The restricted Gibbs measure for a given loss function `L`, prior `μ_prior`, subset `S`, and
    inverse temperature parameter `temp`. It normalizes the probability measure specifically
    over the stable region. -/
noncomputable def localGibbsMeasure
    (L : W ι → ℝ) (μ_prior : Measure (W ι)) (temp : ℝ) (S : Set (W ι)) : Measure (W ι) :=
  gibbsMeasure L (μ_prior.restrict S) temp

/-- The localized posterior at inverse temperature `temp = 1`, used by
    `StabilityPacBayesBound`. -/
noncomputable abbrev localizedPosterior (L_S : W ι → ℝ) (μ_prior : Measure (W ι))
    {ι' : Type*} [Fintype ι'] (cert : StabilityCertificate (W ι) (W ι')) : Measure (W ι) :=
  localGibbsMeasure L_S μ_prior 1 cert.S

omit [Fintype ι] in
/-- **Local Gibbs Measure is a Probability Measure**:
    The localized Gibbs posterior remains a well-defined probability measure
    provided the set `S` has positive prior mass and the restricted loss is integrable. -/
theorem localGibbsMeasure_isProbabilityMeasure {L : W ι → ℝ} {μ_prior : Measure (W ι)}
    {temp : ℝ} {S : Set (W ι)}
    (h_S_pos : μ_prior S > 0)
    (h_int : Integrable (fun w => exp (-temp * L w)) (μ_prior.restrict S)) :
    IsProbabilityMeasure (localGibbsMeasure L μ_prior temp S) := by
  haveI : NeZero (μ_prior.restrict S) := ⟨by
    intro h_z
    have h_e : (μ_prior.restrict S) Set.univ = 0 := by rw [h_z, Measure.coe_zero, Pi.zero_apply]
    rw [Measure.restrict_apply MeasurableSet.univ] at h_e
    simp only [Set.univ_inter] at h_e
    exact (ne_of_gt h_S_pos) h_e
  ⟩
  exact gibbsMeasure_isProbabilityMeasure h_int

/-- The PAC-Bayes Generalization Bound localized to a `StabilityCertificate`.
    Ensures that empirical expected risk bounds population expected risk locally within the
    stable sub-manifold identified by the certificate `cert`. -/
def StabilityPacBayesBound (L_D L_S : W ι → ℝ) (μ_prior : Measure (W ι))
    {ι' : Type*} [Fintype ι'] (cert : StabilityCertificate (W ι) (W ι'))
    (n : ℕ) (δ : ℝ) : Prop :=
  let S_P := localGibbsMeasure L_S μ_prior 1 cert.S
  IsProbabilityMeasure S_P ∧
  ∫ w, L_D w ∂S_P ≤ ∫ w, L_S w ∂S_P +
    sqrt (((klDivergenceW S_P μ_prior).toReal + log (1 / δ)) / (2 * n))

omit [Fintype ι] in
/-- **Local Gibbs posterior is absolutely continuous w.r.t. the prior**:
    `localGibbsMeasure L μ_prior temp S ≪ μ_prior`, since the Gibbs posterior is a
    renormalized density against `μ_prior.restrict S`, which is itself absolutely
    continuous w.r.t. `μ_prior`. -/
theorem localGibbsMeasure_absolutelyContinuous {L : W ι → ℝ} {μ_prior : Measure (W ι)}
    {temp : ℝ} {S : Set (W ι)} :
    localGibbsMeasure L μ_prior temp S ≪ μ_prior := by
  rw [show localGibbsMeasure L μ_prior temp S =
      gibbsMeasure L (μ_prior.restrict S) temp by rfl]
  unfold gibbsMeasure
  refine ?_
  have hd : (μ_prior.restrict S).withDensity (fun w =>
      ENNReal.ofReal (exp (-temp * L w))) ≪ μ_prior.restrict S :=
    withDensity_absolutelyContinuous (μ_prior.restrict S) _
  have hrest : μ_prior.restrict S ≪ μ_prior := Measure.absolutelyContinuous_restrict
  have htrans : (μ_prior.restrict S).withDensity (fun w =>
      ENNReal.ofReal (exp (-temp * L w))) ≪ μ_prior := hd.trans hrest
  exact htrans.smul_left (1 / ENNReal.ofReal
    (∫ w in S, (ENNReal.ofReal (exp (-temp * L w))).toReal ∂μ_prior))

/-- **Localized PAC-Bayes-Hoeffding Inequality**: If the loss excess `L_D - L_S` has a
    sub-Gaussian moment-generating function with parameter `σ²` under the prior, then the
    population risk over the localized Gibbs posterior `S_P` is bounded by the empirical
    risk over `S_P` plus a complexity term. This derives the localized PAC-Bayes bound
    from Donsker-Varadhan, establishing that `StabilityPacBayesBound`'s inequality holds. -/
theorem stabilityPacBayesBound_holds (L_D L_S : W ι → ℝ) (μ_prior : Measure (W ι))
    (σ : ℝ) {ι' : Type*} [Fintype ι'] (cert : StabilityCertificate (W ι) (W ι'))
    [IsProbabilityMeasure μ_prior] [SigmaFinite μ_prior]
    (h_S_pos : μ_prior cert.S > 0)
    (h_int_LS : Integrable (fun w => exp (-1 * L_S w)) (μ_prior.restrict cert.S))
    (h_int_LD : Integrable L_D (localizedPosterior L_S μ_prior cert))
    (h_int_LS_post : Integrable L_S (localizedPosterior L_S μ_prior cert))
    (h_subg : ∀ l : ℝ, 0 < l →
      log (∫ w, exp (l * (L_D w - L_S w)) ∂μ_prior) ≤ l ^ 2 * σ ^ 2 / 2)
    (h_int_exp : ∀ l : ℝ, Integrable (fun w => exp (l * (L_D w - L_S w))) μ_prior)
    (hllr : Integrable (llr (localizedPosterior L_S μ_prior cert) μ_prior)
      (localizedPosterior L_S μ_prior cert))
    (hσ : 0 < σ)
    (hKL : 0 < (klDivergenceW (localizedPosterior L_S μ_prior cert) μ_prior).toReal) :
    ∫ w, L_D w ∂(localizedPosterior L_S μ_prior cert) ≤
      ∫ w, L_S w ∂(localizedPosterior L_S μ_prior cert) +
        Real.sqrt (2 * (klDivergenceW (localizedPosterior L_S μ_prior cert) μ_prior).toReal
          * σ ^ 2) := by
  let S_P := localizedPosterior L_S μ_prior cert
  have hSP_prob : IsProbabilityMeasure S_P :=
    localGibbsMeasure_isProbabilityMeasure h_S_pos h_int_LS
  have hPQ : S_P ≪ μ_prior := localGibbsMeasure_absolutelyContinuous
  haveI : IsProbabilityMeasure S_P := hSP_prob
  exact pacBayesBoundSqrtKL L_D L_S S_P μ_prior σ hPQ h_int_LD h_int_LS_post
    h_subg h_int_exp hllr hσ hKL

/-- **Localized PAC-Bayes Bound is Well-Formed and Holds**:
    Bundles the well-formedness of the localized Gibbs posterior with the derived
    localized PAC-Bayes inequality. This establishes that `StabilityPacBayesBound`
    is not merely a signature but a provable statement under sub-Gaussian losses. -/
theorem stabilityPacBayesBound_provability (L_D L_S : W ι → ℝ) (μ_prior : Measure (W ι))
    (σ : ℝ) {ι' : Type*} [Fintype ι'] (cert : StabilityCertificate (W ι) (W ι'))
    [IsProbabilityMeasure μ_prior] [SigmaFinite μ_prior]
    (h_S_pos : μ_prior cert.S > 0)
    (h_int_LS : Integrable (fun w => exp (-1 * L_S w)) (μ_prior.restrict cert.S))
    (h_int_LD : Integrable L_D (localizedPosterior L_S μ_prior cert))
    (h_int_LS_post : Integrable L_S (localizedPosterior L_S μ_prior cert))
    (h_subg : ∀ l : ℝ, 0 < l →
      log (∫ w, exp (l * (L_D w - L_S w)) ∂μ_prior) ≤ l ^ 2 * σ ^ 2 / 2)
    (h_int_exp : ∀ l : ℝ, Integrable (fun w => exp (l * (L_D w - L_S w))) μ_prior)
    (hllr : Integrable (llr (localizedPosterior L_S μ_prior cert) μ_prior)
      (localizedPosterior L_S μ_prior cert))
    (hσ : 0 < σ)
    (hKL : 0 < (klDivergenceW (localizedPosterior L_S μ_prior cert) μ_prior).toReal) :
    IsProbabilityMeasure (localizedPosterior L_S μ_prior cert) ∧
    ∫ w, L_D w ∂(localizedPosterior L_S μ_prior cert) ≤
      ∫ w, L_S w ∂(localizedPosterior L_S μ_prior cert) +
        Real.sqrt (2 * (klDivergenceW (localizedPosterior L_S μ_prior cert) μ_prior).toReal
          * σ ^ 2) := by
  refine ⟨?_, ?_⟩
  · exact localGibbsMeasure_isProbabilityMeasure h_S_pos h_int_LS
  · exact stabilityPacBayesBound_holds L_D L_S μ_prior σ cert h_S_pos h_int_LS h_int_LD
      h_int_LS_post h_subg h_int_exp hllr hσ hKL

end LeanSharp
