/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

/- Folder-level aggregators for the full LeanSharp library. -/
import LeanSharp.Core
import LeanSharp.Examples
import LeanSharp.Layers
import LeanSharp.Stochastic
import LeanSharp.Tactic
import LeanSharp.Theory

/-!
# LeanSharp Aggregator

This root module exists to provide one import that pulls in the full LeanSharp
library, so downstream users can depend on a stable entrypoint instead of
managing per-submodule imports manually.

It also documents the top-level folder structure so users can quickly decide
whether they need core primitives, layers, stochastic foundations, tactics, or
theory modules when navigating the project.
-/
