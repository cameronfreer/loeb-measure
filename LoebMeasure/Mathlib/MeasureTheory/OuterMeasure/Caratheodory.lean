/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.OuterMeasure.Caratheodory

/-!
# Null sets are Carathéodory measurable

Upstream-oriented material: these declarations concern only mathlib objects and live in
mathlib namespaces. See `LoebMeasure/Mathlib/README.md` for the mirror-path convention,
and issue #10 for the upstreaming proposal.

Promoted here because the Loeb measure's completeness instance must **wrap** these
results rather than reprove them (ADR-0003). Upstream acceptance is nonblocking; local
availability is not.

This module holds only what belongs at mathlib's
`Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`, which is below `Measure` and
knows nothing of it. The measure-layer consequence therefore cannot live here; it is at
`LoebMeasure/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`, mirroring where
`MeasureTheory.Measure.IsComplete` is defined.

## Main results

* `MeasureTheory.OuterMeasure.isCaratheodory_of_measure_zero`: null sets of an outer
  measure are Carathéodory measurable.
-/

open Set

namespace MeasureTheory

variable {α : Type*} {s : Set α}

/-- Null sets of an outer measure are Carathéodory measurable. -/
theorem OuterMeasure.isCaratheodory_of_measure_zero (m : OuterMeasure α) (h : m s = 0) :
    m.IsCaratheodory s := by
  rw [OuterMeasure.isCaratheodory_iff_le']
  intro t
  have h1 : m (t ∩ s) = 0 := le_antisymm ((m.mono inter_subset_right).trans h.le) zero_le
  rw [h1, zero_add]
  exact m.mono sdiff_subset

end MeasureTheory
