/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Completeness from a Carathéodory measurable space

Upstream-oriented material: these declarations concern only mathlib objects and live in
mathlib namespaces. See `LoebMeasure/Mathlib/README.md` for the mirror-path convention.

## Main results

* `MeasureTheory.OuterMeasure.isCaratheodory_of_measure_zero`: null sets of an outer
  measure are Carathéodory measurable.
* `MeasureTheory.Measure.isComplete_of_caratheodory_le`: a measure whose ambient
  measurable space contains the Carathéodory measurable space of its outer measure is
  complete.

Mathlib supplies the opposite inequality `ms ≤ μ.toOuterMeasure.caratheodory`
(`MeasureTheory.le_toOuterMeasure_caratheodory`) for every measure, so the hypothesis
of the second result says exactly that the ambient measurable space *is* the
Carathéodory space. The measurable space is an explicit argument because the intended
callers (measures produced by an outer-measure construction) carry a measurable space
that is not an instance, where ordinary typeclass inference struggles.
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

/-- A measure is complete as soon as its ambient measurable space contains the
Carathéodory measurable space of its outer measure.

Since `MeasureTheory.le_toOuterMeasure_caratheodory` gives the reverse inequality for
every measure, the hypothesis says the two spaces coincide. Measures built from an
outer measure — for instance by `MeasureTheory.AddContent.measureCaratheodory` — satisfy
it with `le_rfl`. -/
theorem Measure.isComplete_of_caratheodory_le (mα : MeasurableSpace α) (μ : @Measure α mα)
    (h : μ.toOuterMeasure.caratheodory ≤ mα) : μ.IsComplete :=
  ⟨fun _ hs ↦ h _ (μ.toOuterMeasure.isCaratheodory_of_measure_zero hs)⟩

end MeasureTheory
