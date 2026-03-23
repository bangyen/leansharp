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

- **Stochastic Robustness**: Proved $O(1/T)$ convergence for SAM under **non-Gaussian/$\alpha$-stable noise**, bridging empirical robustness to formal probability.
- **Statistical Robustness**: Formalized breakdown-point theory for robust estimators, proving the geometric median's **$50\%$ outlier stability** ($k/n \ge 1/2$).
- **Generalization Theory**: Rigorously connected landscape sharpness (max Hessian eigenvalue) to population risk via **PAC-Bayes bounds** and Taylor descent lemmas.
- **Infinite Width Regime**: Established topological dimension sequence limits ($|ι| \to \infty$) for formal **Neural Tangent Kernel (NTK)** and infinite-width analysis.
- **Verified ML Infrastructure**: Hardened the `zsharp_solve` tactic for automated SAM algebra and formalized the stack of modern ML (BatchNorm, ViT, etc.).

## Extensions & Grand Challenges

These items represent specialized research directions currently limited by foundational gaps in Mathlib.

| Task | Necessity | Justification |
| :--- | :--- | :--- |
| **Z-Score CLT** | Medium | Characterizing the statistical limit of the filtered distribution. |
| **Optimality Bound** | Low | Proving statistical lower bounds via information theory. |
| **NTK Dynamics** | Low | Proving network initialization and NTK-regime bounds. |
| **Diffusion Stability**| Low | Formalizing SDE objectives and stability for DDPMs. |

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
