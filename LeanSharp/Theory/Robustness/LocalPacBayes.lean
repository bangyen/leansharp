/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Alignment
import LeanSharp.Theory.Robustness.PacBayesBasis
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

end LeanSharp
