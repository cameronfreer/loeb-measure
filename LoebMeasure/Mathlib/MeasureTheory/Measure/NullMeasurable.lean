/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Mathlib.MeasureTheory.OuterMeasure.Caratheodory
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Completeness from a Carathéodory measurable space

Upstream-oriented material: these declarations concern only mathlib objects and live in
mathlib namespaces. See `LoebMeasure/Mathlib/README.md` for the mirror-path convention,
and issue #10 for the upstreaming proposal.

The path mirrors `Mathlib/MeasureTheory/Measure/NullMeasurable.lean`, where
`MeasureTheory.Measure.IsComplete` is defined — not the lower-level
`Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`, which is below `Measure` and so
could not host this.

Promoted because the Loeb measure's completeness instance must **wrap** this theorem
rather than reprove it (ADR-0003). Upstream acceptance is nonblocking; local
availability is not.

## Main results

* `MeasureTheory.Measure.isComplete_of_caratheodory_le`: a measure whose ambient
  measurable space contains the Carathéodory measurable space of its outer measure is
  complete.

Mathlib supplies the opposite inequality `ms ≤ μ.toOuterMeasure.caratheodory`
(`MeasureTheory.le_toOuterMeasure_caratheodory`) for every measure, so the hypothesis
says exactly that the ambient measurable space *is* the Carathéodory space. The
measurable space is an explicit argument because the intended callers (measures produced
by an outer-measure construction) carry a measurable space that is not an instance,
where ordinary typeclass inference struggles.
-/

namespace MeasureTheory

variable {α : Type*}

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
