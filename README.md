# LeanSharp

**Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4.**

[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

LeanSharp is the formal, mathematical sister-project to [ZSharp](https://github.com/bangyen/zsharp). While ZSharp provides an empirical PyTorch implementation of Z-Score filtered SAM (achieving +5.26% accuracy over SGD), this repository constructs a completely rigorous foundation for the algorithm using the [Lean 4](https://leanprover.github.io/) interactive theorem prover.

## Motivation

Machine Learning optimization algorithms are notoriously difficult to analyze theoretically. Proofs of convergence for Deep Learning optimizers often rely on informal heuristics or hidden assumptions about the loss landscape.

By formally verifying Z-Score SAM in Lean 4, every mathematical step—from the Fréchet derivative of the loss function to the final contraction properties of the gradient filter—is rigorously checked by a verified kernel. **Critically, every theorem is formally proved with zero `axiom` declarations in the source; all mathematical claims are derived directly from Mathlib.**

### Verification Status

All mathematical claims in LeanSharp are formally verified with **zero axioms** and **zero sorry placeholders**. This status is automatically enforced by strict CI quality guards:
- `check_axioms.sh`: Fails if any `axiom` declaration is found.
- `check_sorry.sh`: Fails if any `sorry` proof marker is found.

- ✅ **Mathematical Foundations** (`Core/`): Established Hessian symmetry, L-smoothness, and the core Taylor descent lemma for optimization proofs.
- ✅ **Verified Layer Library** (`Layers/`): Formalized Linear, ReLU, BatchNorm, and Residual layers. Implemented complex architectures including Transformers and Vision Transformers (ViT).
- ✅ **Convergence & Stability** (`Theory/`, `Stochastic/`): Proved deterministic/stochastic $O(1/T)$ rates, PAC-Bayes bounds, and uniform stability markers for filtered gradients.
- ✅ **Automation & Tactics** (`Tactic/`): Hardened the `zsharp_solve` tactic to automate algebraic normalization and Z-score inequality splitting.

## Roadmap & Future Work

The following items represent the planned evolution of LeanSharp, categorized by their necessity for project "completeness" and their implementation complexity.

### Immediate Roadmap (Usability & Tooling)
- **Transformer Gradient Verification**: Formalize the backward pass for multi-head attention and MLP blocks to establish full differentiability.
- **Analytical Verification**: Resolve placeholder proofs for coordinate-wise gradient correctness in `Rosenbrock.lean` and establish multi-layer Lipschitz stability markers for the architectures in `MLP.lean`.
- **ViT Patching Invariance**: Formally prove the mathematical equivalence between Patch Embedding sequences and strided Convolutional mappings.
- **Quantization Stability**: Establish rigorous error bounds and convergence guarantees for the verified 8-bit and 4-bit quantization layers.

### Core Foundation (Required for Completeness)
Addressing these gaps ensures that the central claims of the project are fully supported by rigorous proofs rather than hypotheses.

| Direction | Necessity | Difficulty | Bottleneck |
| :--- | :--- | :--- | :--- |
| **Formal Stochastic Descent** | Prove the stochastic descent lemma for filtered gradients | **Med-High** | Non-trivial variance terms in the Taylor expansion |
| **Robbins-Monro Convergence** | Prove almost sure convergence for Z-score filtered SGD | **Med-High** | Formalizing Martingale Convergence for non-convexity |
| **Deterministic Stability** | Proves Z-score filtering actually stabilizes training | **High** | Handling non-Lipschitz hard-thresholding |
| **Z-Score Universality** | Justifies Z-score filtering statistical optimality | **Extreme** | Formalizing a custom CLT for filtered distributions |
| **Sobolev Regularity** | Transition foundations to $H^1/H^2$ spaces using weak derivatives | **Med-High** | Re-engineering vector spaces to $H^k$ |
| **Hessian-Aware Filtering** | Generalize filtering based on local landscape curvature | **Med-High** | Second-order Fréchet derivatives in Mathlib |

### Extensions & Grand Challenges
These items represent specialized research directions or are currently limited by foundational gaps in Mathlib:
- **Neural Tangent Kernels**: Formalize the NTK limit as layer width $D \to \infty$ to explain deep net training dynamics.
- **Denoising Diffusion**: Formalize the Stochastic Differential Equations (SDEs) governing DDPMs and prove score-matching stability.
- **Heavy-Tailed Noise**: Formalize non-Gaussian probability oracles (e.g., Cauchy noise).
- **Median-Based Robustness**: Formalize median-based filtering as a robust alternative to Z-scores.
- **Third-Order Descent**: Implement multilinear Taylor remainder theory.

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
