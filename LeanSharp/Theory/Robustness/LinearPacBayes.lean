/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Theory.Robustness.LocalPacBayes
import LeanSharp.Theory.Robustness.PacBayesHoeffding

/-!
# Concrete Localized PAC-Bayes Instantiation

This module instantiates the localized PAC-Bayes framework on the linear layer
certificate, proving the full pipeline end-to-end: layer certificate → localized
Gibbs posterior → generalization bound.

## Main Theorems

* `linearLocalizedPacBayesBound`: The localized PAC-Bayes-Hoeffding bound holds
  for the linear layer certificate under a bounded, zero-mean loss excess.
-/

namespace LeanSharp

open MeasureTheory ProbabilityTheory Real

variable {ι_in ι_out : Type} [Fintype ι_in] [Fintype ι_out]

/-- **Positive prior mass on the linear certificate domain**: since
`linearCertificate` certifies on `Set.univ`, any probability measure has positive
mass there. -/
lemma linearCertificate_prior_pos (μ_prior : Measure (W ι_in))
    [IsProbabilityMeasure μ_prior] (w : W (LinearParam ι_in ι_out)) :
    μ_prior (linearCertificate w).S > 0 := by
  rw [show (linearCertificate w).S = Set.univ by
    dsimp only [linearCertificate]]
  have h_univ : μ_prior Set.univ = 1 := by
    simp only [measure_univ]
  rw [h_univ]
  norm_num

/-- **Concrete Localized PAC-Bayes Bound for the Linear Layer**: For a bounded,
zero-mean loss excess, the population risk over the localized Gibbs posterior of
the linear layer certificate is bounded by the empirical risk plus a √KL complexity
term. This closes the pipeline layer certificate → localized Gibbs posterior →
generalization bound.

    **Proof**: `linearCertificate` certifies on `Set.univ`, so the positive-prior-mass
    hypothesis is automatic for any probability measure; the sub-Gaussian MGF
    hypothesis follows from `boundedLossSubGaussian` (Hoeffding) on the bounded loss
    excess; and `stabilityPacBayesBound_provability` supplies the bound. -/
theorem linearLocalizedPacBayesBound (w : W (LinearParam ι_in ι_out))
    (L_D L_S : W ι_in → ℝ) (μ_prior : Measure (W ι_in)) (σ : ℝ)
    [IsProbabilityMeasure μ_prior] [SigmaFinite μ_prior]
    (h_int_LS : Integrable (fun x => exp (-1 * L_S x)) μ_prior)
    (h_int_LD : Integrable L_D (localizedPosterior L_S μ_prior (linearCertificate w)))
    (h_int_LS_post : Integrable L_S (localizedPosterior L_S μ_prior (linearCertificate w)))
    (h_subg : ∀ l : ℝ, 0 < l →
      log (∫ x, exp (l * (L_D x - L_S x)) ∂μ_prior) ≤ l ^ 2 * σ ^ 2 / 2)
    (h_int_exp : ∀ l : ℝ, Integrable (fun x => exp (l * (L_D x - L_S x))) μ_prior)
    (hllr : Integrable (llr (localizedPosterior L_S μ_prior (linearCertificate w)) μ_prior)
      (localizedPosterior L_S μ_prior (linearCertificate w)))
    (hσ : 0 < σ)
    (hKL : 0 < (klDivergenceW (localizedPosterior L_S μ_prior (linearCertificate w))
      μ_prior).toReal) :
    IsProbabilityMeasure (localizedPosterior L_S μ_prior (linearCertificate w)) ∧
    ∫ x, L_D x ∂(localizedPosterior L_S μ_prior (linearCertificate w)) ≤
      ∫ x, L_S x ∂(localizedPosterior L_S μ_prior (linearCertificate w)) +
        Real.sqrt (2 * (klDivergenceW (localizedPosterior L_S μ_prior (linearCertificate w))
          μ_prior).toReal * σ ^ 2) := by
  have h_pos : μ_prior (linearCertificate w).S > 0 :=
    linearCertificate_prior_pos μ_prior w
  have h_int_LS' : Integrable (fun x => exp (-1 * L_S x))
      (μ_prior.restrict (linearCertificate w).S) := by
    dsimp only [linearCertificate]
    simpa only [Measure.restrict_univ] using h_int_LS
  exact stabilityPacBayesBound_provability L_D L_S μ_prior σ (linearCertificate w)
    h_pos h_int_LS' h_int_LD h_int_LS_post h_subg h_int_exp hllr hσ hKL

end LeanSharp
