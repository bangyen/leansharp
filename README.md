# LeanSharp

**Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4.**

[![CI](https://github.com/bangyen/leansharp/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/bangyen/leansharp/actions/workflows/lean_action_ci.yml)
[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

LeanSharp is the formal, mathematical sister project to [ZSharp](https://github.com/bangyen/zsharp). While ZSharp provides an empirical PyTorch implementation of Z-Score filtered SAM, reporting [a 5.26 percentage-point accuracy improvement over SGD](https://github.com/bangyen/zsharp#results), this repository develops a formal foundation for the algorithm using the [Lean 4](https://leanprover.github.io/) interactive theorem prover. Convergence proofs for deep learning optimizers often rely on informal heuristics or hidden assumptions about the loss landscape; the formal proofs here are checked by Lean's trusted kernel, from the Fréchet derivative of the loss function to the contraction properties of the gradient filter.

## Architecture

For a detailed overview of the project's design patterns, including the `W` parameter space abstraction and the recursive `Chain`/`ChainData` architecture, see [ARCHITECTURE.md](ARCHITECTURE.md).

The implementation is organized into `Core` (mathematical primitives), `Layers` (model components), `Stochastic` (optimization and noise models), `Theory` (formal results), `Examples` (concrete instantiations on toy landscapes), and `Tests`.

## Results

- **Robust Convergence**: $O(1/T)$ and $O(1/\sqrt{T})$ stochastic rates for strongly-convex and non-convex objectives under $\alpha$-stable noise; bounded-outlier stability under strict-majority contamination; and geometric convergence of the SAM-ZSharp update ([`zsharp_convergence`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Dynamics/Convergence.lean)) under smoothness, strong convexity, and alignment.
- **Unified Alignment Framework**: The [`AlignmentCondition`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Alignment.lean) bridge linking deterministic gradient geometry to stochastic Z-score filtering.
- **Generalization Theory**: The **ZSharp PAC-Bayes sharpness bound** ([`ZSharpPacBayesBound`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Robustness/PacBayes.lean)) — a pointwise sharpness bound tighter than standard SAM via the filter's $L_2$ contraction, integrating to a distributional expected-risk form.
- **Heavy-Tail Robustness**: Almost-sure convergence of the objective under heavy-tailed Cauchy and $\alpha$-stable noise via non-Gaussian probability oracles ([`zsharp_heavy_tail_convergence`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Stochastic/Convergence/HeavyTail.lean)).
- **Concentration & Infinite-Width Stability**: Discrete vector concentration (Chebyshev) on Z-score mask coverage, plus infinite-width filtered-norm/mean/std domination under convergent gradient norms — the CLT-substitute program ([`Concentration`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Concentration.lean), [`InfiniteLimit`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/InfiniteLimit.lean)).
- **Filter Statistical Guarantees**: Zero filter bias on symmetric heavy-tailed noise (Cauchy, $\alpha$-stable): $E[\mathrm{filteredGradient}\ \eta] = E[\mathrm{zFilteredEmpiricalMean}\ \eta] = 0$ for the sample estimator the algorithm uses ([`FilterBias`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Robustness/FilterBias.lean)).
- **Estimator Breakdown Analysis**: The empirical mean has finite-sample breakdown point $1/n$ ([`mean_breakdown_point_zero`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Robustness/BreakdownPoint.lean)) while the geometric median's is at least $1/2$, with the matching adversarial side ([`geometric_median_breakdown_point_ge_half`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Robustness/BreakdownPoint.lean), [`median_breakdown`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Robustness/MedianComparison/Breakdown.lean)); under a strict-majority fixed subset, one movable outlier drives the mean unbounded while the median stays bounded ([`median_bounded_mean_unbounded_one_outlier_of_majority`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Robustness/ComparisonResults.lean)).
- **SAM Non-Convex Rate**: The conditional $O(1/\sqrt{T})$ result with explicit $2L^2\rho^2$ perturbation penalty ([`sam_nonconvex_rate_complete`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Stochastic/Foundations/Schedules/SamNonconvex.lean), [`SAMDescent`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Stochastic/Convergence/Process/SamDescent.lean), [`SAMOracle`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Stochastic/Foundations/SAMOracle.lean)).

## Immediate Roadmap

| Task | Priority | Details |
| :--- | :--- | :--- |
| **Genuinely-Random Noise Instantiation** | Low | The noise hypotheses (`IsStochasticGradient`, `HasBoundedVariance`) are shown satisfiable only in the deterministic `PUnit` case. Instantiate a genuinely random two-point noise on the quadratic bowl, which requires a uniform probability measure on a finite type that mathlib does not provide out of the box. |
| **Full-Stack Concrete Stochastic Instantiation** | Low | No concrete noise satisfies the *complete* hypothesis stack (stochastic gradient + variance + alignment) of a descent or rate theorem. Instantiate one that does and fire it through `z_score_descent` or a rate result, making the headline results non-vacuous end-to-end. The alignment hypothesis is the hard part. |
| **Concrete Geometric Alignment** | Low | Every `zsharp_convergence` test takes `AlignmentCondition` as an assumption; nothing proves it holds for a concrete gradient. Establishing it for `toyLoss`/`advancedLoss` (even unfiltered) requires WithLp-smul, inner-product, and filter computations that proved fiddly in an initial attempt. |

## Scope & Limitations

**Robustness.** The filter's robustness guarantee is the bounded-outlier type — the filtered mean stays
bounded when a strict majority of points are fixed and the outliers are bounded
(`z_filtered_empirical_mean_bounded_subset`, `median_and_zfiltered_mean_bounded_subset`). It is not
breakdown-robust in the unbounded sense: a single concentrated outlier vector (σ = 0) passes the per-vector
mask untouched, so the strict finite-sample breakdown point is zero, as for the ordinary mean.

**Scope.** This project verifies the Z-Score filtered SAM algorithm itself — its convergence, stability,
robustness, and the statistical properties of the filter. Within generalization, it develops pointwise and
distributional PAC-Bayes **sharpness** bounds (`ZSharpPacBayesBound`), but deliberately does not develop the
full KL-divergence PAC-Bayes risk form (with prior/posterior complexity term) or convergence results that
require idealized assumptions unmet by deep networks; that material is out of scope.

**Conditional SAM rate.** The $O(1/\sqrt{T})$ non-convex rate (`sam_nonconvex_rate_complete`) holds
conditional on the `SAMDescentEnvelope` premise. Two supporting results are formalized —
`zsharp_envelope_of_pointwise_descent` (the conditional-expectation/measurability bridge) and
`sam_stochastic_descent_step_effective` (the one-step bound in quarter-gradient effective-variance form) —
but deriving the envelope itself for the filtered sequence requires conditional martingale-noise machinery
that this project does not develop, so the rate is stated conditionally.

**Heavy-tail oracles.** The `AlphaStableProbabilityOracle`/`CauchyProbabilityOracle` predicates are
polynomial-tail *upper bounds* (`ℙ[‖ξ‖ ≥ r] ≤ C/r^α`), and any bounded noise satisfies them. The heavy-tail
convergence theorem therefore applies to bounded noise as well; the "heavy-tailed" framing is stronger than
what the oracle predicates enforce.

**CLT.** The discrete Z-score mask is a discontinuous function, so a classical Central Limit Theorem for the
filtered gradient is not formally derivable here. Instead, the project provides non-asymptotic concentration
(discrete Chebyshev) and infinite-width filtered-statistic domination as the CLT substitute — formalized in
`Theory/Concentration` and `Theory/InfiniteLimit`.

## Installation & Building

Make sure you have [elan](https://github.com/leanprover/elan) installed for Lean 4 version management.

```bash
git clone https://github.com/bangyen/leansharp.git
cd leansharp
lake exe cache get  # Downloads the pre-compiled Mathlib libraries
lake build
```

## Contributing
This repo uses standard Mathlib naming conventions. If you're a Lean 4 wizard interested in ML optimization theory, feel free to submit PRs targeting the roadmap!

## Citation

If you use this work in your research, please cite:

```bibtex
@misc{pham_leansharp_2026,
  author = {Pham, Bangyen},
  title = {LeanSharp: Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4},
  year = {2026},
  url = {https://github.com/bangyen/leansharp}
}
```
