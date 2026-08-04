# LeanSharp

**Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4.**

[![CI](https://github.com/bangyen/leansharp/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/bangyen/leansharp/actions/workflows/lean_action_ci.yml)
[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

LeanSharp is the formal, mathematical sister project to [ZSharp](https://github.com/bangyen/zsharp). While ZSharp provides an empirical PyTorch implementation of Z-Score filtered SAM, reporting [a 5.26 percentage-point accuracy improvement over SGD](https://github.com/bangyen/zsharp#results), this repository develops a formal foundation for the algorithm using the [Lean 4](https://leanprover.github.io/) interactive theorem prover. Convergence proofs for deep learning optimizers often rely on informal heuristics or hidden assumptions about the loss landscape; the formal proofs here are checked by Lean's trusted kernel, from the Fréchet derivative of the loss function to the contraction properties of the gradient filter.

## Architecture

For a detailed overview of the project's design patterns, including the `W` parameter space abstraction and the recursive `Chain`/`ChainData` architecture, see [ARCHITECTURE.md](ARCHITECTURE.md).

The implementation is organized into `Core` (mathematical primitives), `Layers` (model components), `Stochastic` (optimization and noise models), `Theory` (formal results), and `Tests`.

## Results

- **Robust Convergence**: $O(1/T)$ stochastic convergence under $\alpha$-stable noise, with matching $O(1/T)$ (strongly convex) and $O(1/\sqrt{T})$ (non-convex) rates; $50\%$ breakdown-point outlier stability; and geometric convergence of the SAM-ZSharp update ([`zsharp_convergence`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Dynamics/Convergence.lean)) under smoothness, strong convexity, and the alignment condition.
- **Unified Alignment Framework**: The [`AlignmentCondition`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Alignment.lean) bridge linking deterministic gradient geometry to stochastic Z-score filtering.
- **Formal Stability & Regularity**: [`StabilityCertificate`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Alignment.lean) $C^2$ smoothness and Lipschitz regularity for `Linear`, `Softmax`, `Attention`, `LayerNorm`, and `BatchNorm`; layer-wise Z-score filtering bounds the total update norm by the raw backprop gradients, and the mask is scale-invariant.
- **Generalization Theory**: The **ZSharp PAC-Bayes sharpness bound** ([`ZSharpPacBayesBound`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Robustness/PacBayes.lean)) — the filtered gradient satisfies a pointwise sharpness bound provably tighter than standard SAM via the filter's $L_2$ contraction, integrating to a distributional expected-risk form.
- **Heavy-Tail Robustness**: Almost-sure convergence of the objective under heavy-tailed noise (Cauchy, $\alpha$-stable) via non-Gaussian probability oracles ([`HeavyTail`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Stochastic/Convergence/HeavyTail.lean)).
- **Concentration & Infinite-Width Stability**: Discrete vector concentration (Chebyshev) on Z-score mask coverage, plus infinite-width filtered-norm/mean/std domination under convergent gradient norms — the CLT-substitute program ([`Concentration`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Concentration.lean), [`InfiniteLimit`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/InfiniteLimit.lean)).
- **Filter Statistical Guarantees**: Zero filter bias on symmetric heavy-tailed noise (Cauchy, $\alpha$-stable): $E[\mathrm{filteredGradient}\ \eta] = E[\mathrm{zFilteredEmpiricalMean}\ \eta] = 0$ for the sample estimator the algorithm uses ([`FilterBias`](https://github.com/bangyen/leansharp/blob/main/LeanSharp/Theory/Robustness/FilterBias.lean)).

## Immediate Roadmap

| Task | Priority | Details |
| :--- | :--- | :--- |
| **Conditional Non-Convex SAM-ZSharp Rate** | Medium | The complete $O(1/\sqrt{T})$ rate is formalized in `sam_nonconvex_rate_complete` under the conditional `SAMDescentEnvelope`, with perturbation penalty $2L^2\rho^2$. **Remaining:** derive that conditional envelope for the filtered sequence from `sam_stochastic_descent_step`, including the required filtration and measurability bridge. |
| **Conditional Oracle Model** | Medium | Introduce a generic adapted filtration with conditional martingale-noise and variance assumptions at the SAM-perturbed point, then instantiate `SAMDescentEnvelope` without modeling dataset sampling or architecture-specific randomness. |

## Scope & Limitations

> **Note on the Z-Score filter's robustness**: the filter's robustness guarantee is the bounded-outlier
> type — the filtered mean stays bounded when a strict majority of points are fixed and the outliers are
> bounded (`z_filtered_empirical_mean_bounded_subset`, `median_and_zfiltered_mean_bounded_subset`). It is
> not breakdown-robust in the unbounded sense: a single concentrated outlier vector (σ = 0) passes the
> per-vector mask untouched, so the strict finite-sample breakdown point is zero, as for the ordinary mean.

> **Scope.** This project verifies the Z-Score filtered SAM algorithm itself — its convergence, stability,
> robustness, and the statistical properties of the filter. Within generalization, it develops pointwise and
> distributional PAC-Bayes **sharpness** bounds (`ZSharpPacBayesBound`), but deliberately does not develop the
> full KL-divergence PAC-Bayes risk form (with prior/posterior complexity term) or convergence results that
> require idealized assumptions unmet by deep networks; that material is out of scope.

> **Note on the Z-Score CLT**: The discrete Z-score mask is a discontinuous function, so
> a classical Central Limit Theorem for the filtered gradient is not formally derivable here.
> Instead, the project provides non-asymptotic concentration (discrete Chebyshev) and
> infinite-width filtered-statistic domination as the CLT substitute — formalized in
> `Theory/Concentration` and `Theory/InfiniteLimit`.

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
