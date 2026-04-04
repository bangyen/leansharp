# Deep-Dive API Consistency Analysis: LeanSharp

This report analyzes structural, mathematical, and architectural inconsistencies identified within the `LeanSharp` project. These findings represent "deep" inconsistencies that affect the library's formal integrity and maintainability.

---

## 1. Divergent Stability Logic [x]
There is a fundamental inconsistency in how numerical stability is handled across normalization modules.
- **Transformer Block** (`Transformer.lean`): Integrates a hard-coded epsilon (`0.00001`) into its internal feature normalization: `Real.sqrt ((∑ i, (row i - μ_s)^2) / D + 0.00001)`.
- **BatchNorm** (`BatchNorm.lean`): Now uses same epsilon (`0.00001`).
- **LayerNorm** (`LayerNorm.lean`): Now uses same epsilon (`0.00001`).
- **Status**: **RESOLVED**. All normalization components now use the same stability constant `0.00001`.

## 2. Redundant Module Duplication [x]
The `Transformer` module exhibits a significant architectural flaw.
- **Violation**: Instead of using the centrally defined `layerNorm` from `LeanSharp.Layers.Normalization.LayerNorm`, the `Transformer` module re-implements the logic as `featureNormForward`.
- **Status**: **RESOLVED**. `Transformer.lean` now utilizes `layernormForward` from the central module, eliminating redundant normalization logic.

## 3. Dependency Hierarchy Violation [x]
The project's architectural layers are "tangled" at the core.
- **Violation**: `LeanSharp/Core/Models.lean` imports `LeanSharp/Stochastic/Mechanics/SampleErrors.lean`.
- **Status**: **RESOLVED**. The phantom dependency has been removed from `Models.lean`.

## 4. Patchy Proof Coverage [x]
The "Proof-Oriented" pillar of the API is applied inconsistently across the `Layers` module.
- **Status**: **RESOLVED**. The `StabilityCertificate` contract has been fully implemented across all core layers (`Linear`, `LayerNorm`, `BatchNorm`), ensuring a standardized foundation for structural analysis.

## 5. Theorem Naming Logic Conflict [x]
The naming convention for theorems diverges between modules.
- **Status**: **RESOLVED**. Naming and docstrings in the `Stochastic` modules have been standardized to match the `snake_case` theorem convention and fix "Ghost Theorem" mismatches.

---

## Conclusion
LeanSharp's documentation mirrors a consistency that the underlying code has started to outgrow. Specifically, the **Transformer Duplication** and **Epsilon Divergence** represent significant technical debt that undermines the project's goal of rigorous formal verification.
