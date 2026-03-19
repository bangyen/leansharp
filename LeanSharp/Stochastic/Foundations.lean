/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Stochastic.Foundations.Integrability
import LeanSharp.Stochastic.Foundations.Martingale
import LeanSharp.Stochastic.Foundations.Oracles
import LeanSharp.Stochastic.Foundations.RobbinsMonro
import LeanSharp.Stochastic.Foundations.Schedules

/-!
# Stochastic Foundations Aggregator

This module exists to centralize integrability, martingale, oracle, and
schedule prerequisites so convergence modules can depend on one foundation
entrypoint.
-/
