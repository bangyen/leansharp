/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

/- Folder-level aggregators for all test suites. -/
import Tests.Functional
import Tests.Landscape
import Tests.Structural
import Tests.Theory

/-!
# Test Suite Aggregator

This root test module exists to gather all LeanSharp test modules under one
import target, making CI and local verification commands simpler.

It also serves as a folder-level map for the test suite by separating
functional, landscape, and structural coverage areas.
-/
