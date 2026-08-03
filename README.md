# LeanSharp

**Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4.**

[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

LeanSharp is the formal, mathematical sister-project to [ZSharp](https://github.com/bangyen/zsharp). While ZSharp provides an empirical PyTorch implementation of Z-Score filtered SAM (achieving +5.26% accuracy over SGD), this repository constructs a completely rigorous foundation for the algorithm using the [Lean 4](https://leanprover.github.io/) interactive theorem prover.

## Motivation

Machine Learning optimization algorithms are notoriously difficult to analyze theoretically. Proofs of convergence for Deep Learning optimizers often rely on informal heuristics or hidden assumptions about the loss landscape.

By formally verifying Z-Score SAM in Lean 4, every mathematical step—from the Fréchet derivative of the loss function to the final contraction properties of the gradient filter—is rigorously checked by a verified kernel.

## Architecture

For a detailed overview of the project's design patterns, including the `W` parameter space abstraction and the recursive `Chain`/`ChainData` architecture, see [ARCHITECTURE.md](ARCHITECTURE.md).

## Key Accomplishments

- **Robust Convergence Theory**: Proved $O(1/T)$ stochastic convergence under $\alpha$-stable noise and a matching $O(1/T)$ rate for strongly convex objectives, plus an $O(1/\sqrt{T})$ rate for non-convex objectives. Established $50\%$ outlier stability through formalized breakdown-point analysis.
- **Unified Alignment Framework**: Established the definitive `AlignmentCondition` bridge, mathematically linking deterministic gradient geometry to stochastic Z-score filtering.
- **Formal Stability & Regularity**: Completed `StabilityCertificate` $C^2$ smoothness and Lipschitz regularity proofs for the entire core stack, including `Linear`, `Softmax`, `Attention`, `LayerNorm`, and `BatchNorm`. Proved that layer-wise Z-score filtering bounds the total network update norm by the raw backpropagation gradients, and that the Z-score mask is scale-invariant.
- **Generalization Theory**: Proved the **Donsker-Varadhan Variational Inequality** using Mathlib's information-theoretic machinery, and derived from it the $\lambda$-parametrized PAC-Bayes-Hoeffding inequality, its $\sqrt{\text{KL}}$ form under a sub-Gaussian MGF assumption, a Hoeffding bridge from bounded losses, and localized bounds over `StabilityCertificate` regions — instantiated end-to-end on the linear layer certificate for non-convex landscapes. Derived the finite-sample **McAllester bound with confidence**: with probability at least $1-\delta$ over an i.i.d. sample of size $n$, the population risk of a fixed posterior is at most its empirical risk plus $\sqrt{(\text{KL}(P\|\mu)+\log(1/\delta))/(2n)}$ — and instantiated it on the Z-Score filtered objective, bounding the posterior risk by the better of the $\sqrt{\text{KL}}$ sample term and the filtered-sharpness penalty.
- **Heavy-Tail Robustness**: Proved almost-sure convergence of the objective under heavy-tailed noise (Cauchy, $\alpha$-stable) via non-Gaussian probability oracles.
- **Concentration & Infinite-Width Stability**: Formalized discrete vector concentration (Chebyshev) bounding the Z-score mask coverage, plus infinite-width filtered-norm, filtered-mean, and filtered-std domination under convergent gradient norms — completing the CLT-substitute program.

## Immediate Roadmap

| Task | Priority | Justification |
| :--- | :--- | :--- |
| **McAllester Bound for All Posteriors** | Medium | The fixed-posterior McAllester bound $\sqrt{(\text{KL}(P\|\mu)+\log(1/\delta))/(2n)}$ is proven (`PacBayesMcAllesterBound`); the simultaneous "for all posteriors" form requires a discretization/union bound over the posterior space. |
| **Chain-Level Convergence** | Medium | Extend convergence from single layers to composed `Chain` architectures. This requires the composed loss to be strongly convex in the flattened parameters (an idealized assumption) and a certificate-based smoothness composition argument; a genuine treatment is still open. |

> **Note on the Z-Score CLT**: The discrete Z-score mask is a discontinuous function, so
> a classical Central Limit Theorem for the filtered gradient is not formally derivable here.
> Instead, the project provides non-asymptotic concentration (discrete Chebyshev) and
> infinite-width filtered-statistic domination as the CLT substitute — formalized in
> `Theory/Concentration` and `Theory/InfiniteLimit`.

## Extensions & Future Work

| Task | Priority | Justification |
| :--- | :--- | :--- |
| **Optimality Bound** | Low | Prove statistical lower bounds via information theory. |

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
