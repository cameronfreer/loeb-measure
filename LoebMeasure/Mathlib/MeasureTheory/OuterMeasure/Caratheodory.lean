/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.OuterMeasure.Caratheodory

/-!
# Null sets and transported sets are Carathéodory measurable

Upstream-oriented material: these declarations concern only mathlib objects and live in
mathlib namespaces. See `LoebMeasure/Mathlib/README.md` for the mirror-path convention.
Two upstreaming proposals share this file: issue #10 for the null-set lemma, and issue
#121 for the transport lemma.

The null-set lemma is promoted here because the Loeb measure's completeness instance must
**wrap** it rather than reprove it (ADR-0003). Upstream acceptance is nonblocking; local
availability is not. Its measure-layer consequence cannot live here, since mathlib's
`Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean` is below `Measure` and knows
nothing of it; it is at `LoebMeasure/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`,
mirroring where `MeasureTheory.Measure.IsComplete` is defined.

The transport lemma is what the graded layer's permutation invariance uses to carry
Carathéodory measurability along a coordinate permutation.

## Main results

* `MeasureTheory.OuterMeasure.isCaratheodory_of_measure_zero`: null sets of an outer
  measure are Carathéodory measurable.
* `MeasureTheory.OuterMeasure.IsCaratheodory.preimage_of_leftInverse`: a map with a left
  inverse under which the outer measure is invariant preserves Carathéodory
  measurability.
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

/-- Carathéodory measurability is preserved by a map `f` with a left inverse `g`, when the
outer measure is invariant under preimages along `f`. The left inverse is what lets a test
set `t` be written as `f ⁻¹' (g ⁻¹' t)`, so that the Carathéodory identity for `s` at
`g ⁻¹' t` transports to the identity for `f ⁻¹' s` at `t`. -/
theorem OuterMeasure.IsCaratheodory.preimage_of_leftInverse {m : OuterMeasure α}
    {f g : α → α} (hgf : Function.LeftInverse g f) (hm : ∀ s, m (f ⁻¹' s) = m s)
    (hs : m.IsCaratheodory s) : m.IsCaratheodory (f ⁻¹' s) := by
  intro t
  have ht : f ⁻¹' (g ⁻¹' t) = t := by
    ext x
    simp [hgf x]
  calc m t = m (g ⁻¹' t) := by rw [← hm (g ⁻¹' t), ht]
    _ = m (g ⁻¹' t ∩ s) + m (g ⁻¹' t \ s) := hs _
    _ = m (f ⁻¹' (g ⁻¹' t ∩ s)) + m (f ⁻¹' (g ⁻¹' t \ s)) := by rw [hm, hm]
    _ = m (t ∩ f ⁻¹' s) + m (t \ f ⁻¹' s) := by
      rw [Set.preimage_inter, Set.preimage_sdiff, ht]

end MeasureTheory
