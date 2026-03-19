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
- `check_banned.sh`: Fails if banned Lean markers are found (`axiom`, `sorry`, `admit`, `nolint`, file-level `set_option`).
- `check_import.sh`: Fails if banned or disallowed imports are detected.
- `check_simp.sh`: Fails if risky simplification patterns are detected.

Run all guards locally with:

```bash
./scripts/check_all.sh
```

- ✅ **Mathematical Foundations** (`Core/`): Established Hessian symmetry, L-smoothness, and the core Taylor descent lemma for optimization proofs.
- ✅ **Verified Layer Library** (`Layers/`): Formalized Linear, ReLU, BatchNorm, and Residual layers. Implemented complex architectures including Transformers and Vision Transformers (ViT).
- ✅ **SAM Logic & Invariance** (`Theory/`): Formalized the mathematical definition of the Z-Score SAM update step and proved the functional equivalence of patch embeddings to strided 2D convolutions.
- ✅ **Stochastic & Heavy-Tailed Convergence** (`Stochastic/`): Proved deterministic/stochastic $O(1/T)$ rates and established almost-sure convergence under **heavy-tailed noise regimes** using new Cauchy/non-Gaussian/$\alpha$-stable probability oracle interfaces.
- ✅ **Second-Order Dynamics** (`Theory/`): Formalized the **Second-Order Descent Lemma** using the local curvature matrix and generalized filter condition, bridging structural filter contract properties to functional descent.
- ✅ **Automation & Tactics** (`Tactic/`): Hardened the `zsharp_solve` tactic to automate algebraic normalization and Z-score inequality splitting.
- ✅ **Multilinear Taylor** (`Core/`): Generalization of the project-specific Taylor bounds to arbitrary-degree multilinear forms.

## Roadmap & Future Work

The following items represent the planned evolution of LeanSharp. While the project is **functionally complete** (core convergence results are verified), the roadmap aims for **theoretical completeness** and foundational rigor.

### Immediate Roadmap (Hard Complexity)

These items represent foundational tasks necessary for project completeness and Mathlib alignment.

| Task | Necessity | Justification |
| :--- | :--- | :--- |
| **Higher-Order Fréchet** | Low | Core results use custom `hessian`; needs Mathlib alignment. |
| **Analytical Limit $D \to \infty$** | Medium | Foundation for analyzing generalization in infinite-width layers. |

---

### Extensions & Grand Challenges (Extreme Complexity)

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
