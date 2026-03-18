/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import Tests.Functional.Integrability
import Tests.Functional.RobbinsMonro
import Tests.Functional.RobustMethods
import Tests.Functional.SobolevSpace
import Tests.Landscape.CosineDecays
import Tests.Landscape.HardThresholds
import Tests.Landscape.IllConditioned
import Tests.Landscape.QuadraticBowl
import Tests.Structural.LearningRates
import Tests.Structural.NetworkLayers
import Tests.Structural.StabilityProps
import Tests.Structural.TacticSystems

/-!
# Test Suite Aggregator

This root test module exists to gather all LeanSharp test modules under one
import target, making CI and local verification commands simpler.
-/
