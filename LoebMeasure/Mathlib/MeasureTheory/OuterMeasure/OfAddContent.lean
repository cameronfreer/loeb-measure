/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Mathlib.MeasureTheory.OuterMeasure.Caratheodory
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

/-!
# Completeness of the measure built from an additive content

Upstream-oriented material: these declarations concern only mathlib objects and live in
mathlib namespaces. See `LoebMeasure/Mathlib/README.md` for the mirror-path convention.

## Main results

* `MeasureTheory.AddContent.measureCaratheodory_isComplete`: the measure produced by
  `MeasureTheory.AddContent.measureCaratheodory` is complete.

The proof is a one-line corollary of
`MeasureTheory.Measure.isComplete_of_caratheodory_le`: that measure is *defined* on the
Carathéodory measurable space of the induced outer measure, and agrees with it on every
set, so the required inequality is `le_rfl`.
-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)}

/-- The measure produced by `MeasureTheory.AddContent.measureCaratheodory` is complete.

No finiteness or probability hypotheses are needed: the measure is defined on the
Carathéodory measurable space of the induced outer measure and agrees with that outer
measure on every set, so a null set is Carathéodory measurable, hence measurable. -/
theorem AddContent.measureCaratheodory_isComplete (m : AddContent ℝ≥0∞ C)
    (hC : IsSetSemiring C) (hsub : m.IsSigmaSubadditive) :
    (m.measureCaratheodory hC hsub).IsComplete :=
  Measure.isComplete_of_caratheodory_le _ _ le_rfl

end MeasureTheory
