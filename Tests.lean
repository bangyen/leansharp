/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

/- Functional tests: assumptions and theorem-level behavior checks. -/
import Tests.Functional.HeavyTail
import Tests.Functional.Integrability
import Tests.Functional.RobbinsMonro
import Tests.Functional.SobolevSpace

/- Landscape tests: concrete objective/optimizer examples and sanity checks. -/
import Tests.Landscape.CosineDecays
import Tests.Landscape.HardThresholds
import Tests.Landscape.IllConditioned
import Tests.Landscape.QuadraticBowl

/- Structural tests: layer architecture contracts and stability regressions. -/
import Tests.Structural.LearningRates
import Tests.Structural.NetworkLayers
import Tests.Structural.SecondOrder
import Tests.Structural.StabilityProps
import Tests.Structural.TacticSystems

/-!
# Test Suite Aggregator

This root test module exists to gather all LeanSharp test modules under one
import target, making CI and local verification commands simpler.

It also serves as a folder-level map for the test suite by separating
functional, landscape, and structural coverage areas.
-/
