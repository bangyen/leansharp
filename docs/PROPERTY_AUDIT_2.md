# Deep-Dive Property Consistency Audit: LeanSharp Functional Gaps

This report identifies four critical inconsistencies in the *mathematical properties and proofs* provided across the `LeanSharp` library.

---

## 1. The Lipschitz Certification Gap [x]
While the library strives to be "proof-oriented," there is a stark disparity in how stability properties are certified across layers.
- **Status**: **RESOLVED**. Core layers (`Linear`, `LayerNorm`, `BatchNorm`) now provide `StabilityCertificate` instances, bridging the gap between implementation and structural theory.

## 2. Conceptual Divergence in "Alignment" [x]
The project uses two different mathematical frameworks for the "Alignment" property, making them functionally incompatible.
- **Status**: **RESOLVED**. Both frameworks are now unified in `Theory/Alignment.lean` via `AlignmentCondition` and `StochasticAlignmentCondition`, with a formal bridge theorem `alignment_condition_of_signal_noise`.

## 3. Redundant Statistical Kernels [x]
Despite having a centralized `Stats.lean` module, the library duplicates its core logic without proof inheritance.
- **Status**: **RESOLVED**. `BatchNorm` and `LayerNorm` have been refactored to use the centralized `vectorNormalize` primitive in `Stats.lean`, ensuring proof inheritance for statistical identities.

## 4. Regularity Contradiction (C2 vs. C0) [x]
The library exhibits a high-level theoretical inconsistency regarding function regularity.
- **Status**: **RESOLVED**. `smoothReluLayer` (Softplus) has been introduced and formally proven to be `ContDiff ℝ 2` in `Layers/Basic/Activation.lean`, satisfying the second-order requirements.

---

## Conclusion
The recent refactoring addressed naming and constants, but the **philosophical and mathematical gaps** between files remain. Bridging the $C^2/C^0$ contradiction and unifying the "Alignment" and "Stability" contracts should be the next priorities for a truly consistent API.
