/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

/- Core: foundational primitives reused across optimization and proof modules. -/
import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import LeanSharp.Core.Models
import LeanSharp.Core.Objective
import LeanSharp.Core.Stats
import LeanSharp.Core.Taylor

/- Examples: concrete objectives/networks used for demos and regression checks. -/
import LeanSharp.Examples.IllConditioned
import LeanSharp.Examples.PerceptronNetwork
import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Examples.Rosenbrock

/- Layers: reusable NN components grouped by modeling role. -/
-- Architectures: composed multi-block systems (attention/transformer/ViT).
import LeanSharp.Layers.Architectures.Attention
import LeanSharp.Layers.Architectures.Transformer
import LeanSharp.Layers.Architectures.VisionTransformer

-- Basic: elemental feedforward layers and activation-style components.
import LeanSharp.Layers.Basic.Activation
import LeanSharp.Layers.Basic.Dropout
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Layers.Basic.Residual

-- Normalization: stabilization and feature-scaling operators.
import LeanSharp.Layers.Normalization.BatchNorm
import LeanSharp.Layers.Normalization.LayerNorm

-- Specialized: domain-specific layers such as convolution and quantization.
import LeanSharp.Layers.Specialized.Convolution
import LeanSharp.Layers.Specialized.Quantization

/- Stochastic: noisy-gradient assumptions, steps, and asymptotic guarantees. -/
-- Convergence: process-level bridge assumptions and convergence statements.
import LeanSharp.Stochastic.Convergence.Process
import LeanSharp.Stochastic.Convergence.Bridges
import LeanSharp.Stochastic.Convergence.Assumptions
import LeanSharp.Stochastic.Convergence.HeavyTail

-- Mechanics: one-step descent identities and stochastic decomposition lemmas.
import LeanSharp.Stochastic.Mechanics.DescentSteps
import LeanSharp.Stochastic.Mechanics.SampleErrors
import LeanSharp.Stochastic.Mechanics.SharpnessMap

-- Foundations: integrability, martingale, oracle, and schedule prerequisites.
import LeanSharp.Stochastic.Foundations.Integrability
import LeanSharp.Stochastic.Foundations.Martingale
import LeanSharp.Stochastic.Foundations.Oracles
import LeanSharp.Stochastic.Foundations.Schedules
import LeanSharp.Stochastic.Foundations.RobbinsMonro

/- Tactics: project-local automation for recurring proof patterns. -/
import LeanSharp.Tactic.ZSolve

/- Theory: higher-level mathematical guarantees for LeanSharp methods. -/
-- Dynamics: training dynamics, rates, bounds, and limiting behavior.
import LeanSharp.Theory.Dynamics.Convergence
import LeanSharp.Theory.Dynamics.Generalization
import LeanSharp.Theory.Dynamics.SamBound
import LeanSharp.Theory.Dynamics.Schedulers
import LeanSharp.Theory.Dynamics.SecondOrder
import LeanSharp.Theory.Dynamics.Universality

-- Structural: architectural invariance, smoothness, and stability results.
import LeanSharp.Theory.Structural.ChainStability
import LeanSharp.Theory.Structural.FilterAlgebra
import LeanSharp.Theory.Structural.HardThresholding
import LeanSharp.Theory.Structural.HessianContraction
import LeanSharp.Theory.Structural.SAMDifferentiability
import LeanSharp.Theory.Structural.StabilityProperties
import LeanSharp.Theory.Structural.ViTInvariance
import LeanSharp.Theory.Structural.SobolevRegularity

-- Robustness: contamination sensitivity and estimator-comparison guarantees.
import LeanSharp.Theory.Robustness.BreakdownPoint
import LeanSharp.Theory.Robustness.ComparisonResults
import LeanSharp.Theory.Robustness.FilteredMeanProps
import LeanSharp.Theory.Robustness.MedianComparison
import LeanSharp.Theory.Robustness.SensitivityBounds

/-!
# LeanSharp Aggregator

This root module exists to provide one import that pulls in the full LeanSharp
library, so downstream users can depend on a stable entrypoint instead of
managing per-submodule imports manually.

It also documents the top-level folder structure so users can quickly decide
whether they need core primitives, layers, stochastic foundations, tactics, or
theory modules when navigating the project.
-/
