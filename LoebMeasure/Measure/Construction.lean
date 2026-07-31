/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The Loeb-measure constructor route (D0.3 spike)

D0.3 spike (issue #3, ADR-0003): exercise the candidate route

```
sigma-subadditive AddContent on a set semiring
  → AddContent.measureCaratheodory
```

at the pinned mathlib revision and inventory what remains substantive for the
internal-mod-null characterization.

The generic completeness results this spike produced are **not** here: they concern
only mathlib objects and live under `LoebMeasure/Mathlib/MeasureTheory/OuterMeasure/`
as independently upstreamable modules. This file keeps only the spike fixtures and the
inventory.

## Toy construction

A Dirac content at `0` on the full powerset of `ℕ`, run through the route end to end:
`AddContent` fields, `IsSetSemiring`, `IsSigmaSubadditive`, `measureCaratheodory`, the
extension property (`toyMeasure_apply`), a probability-measure instance, and the
completeness instance obtained by *wrapping* the generic theorem.

## Inventory: what remains substantive for internal-mod-null (C7/C8)

The route above does **not** by itself give
`loebMeasurable_iff_internal_mod_null`. Remaining obligations, in dependency order:

1. realized internal carriers form an `IsSetSemiring` (M2, unit I3);
2. sigma-subadditivity of the internal content via the diagonal lemma: a decreasing
   sequence of internal sets with empty intersection is eventually empty, giving
   continuity at `∅`, then `addContent_iUnion_eq_sum_of_tendsto_zero` and
   `isSigmaSubadditive_of_addContent_iUnion_eq_tsum` (M3, unit C5);
3. outer-measure approximation: for a Carathéodory-measurable `s`, unfold
   `inducedOuterMeasure` (an infimum over countable covers by semiring elements) to
   get, for every `ε > 0`, a countable internal cover of `s` with total content within
   `ε` — this uses **finite total mass**;
4. the increasing-envelope form of the diagonal lemma (M2, unit I6) to replace the
   countable internal cover by a *single* internal set containing `s` with content
   within `ε`, and symmetrically inside `sᶜ`;
5. combining 3 and 4 yields `exists_internal_symmDiff_lt` and then
   `loebMeasurable_iff_internal_mod_null` (M3, units C7/C8).

Steps 3–5 are genuine approximation theorems consuming saturation and finite mass;
they are not formal consequences of the Carathéodory construction. This matches the
boundary drawn in ADR-0003.

Declaration names are provisional until the M3 units land.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Loeb

/-! ### Toy construction: a Dirac content through the full route -/

/-- Toy content for the D0.3 spike: the Dirac content at `0` on the full powerset of
`ℕ`. Spike-only; the real internal content replaces it at M3. -/
noncomputable def diracContent : AddContent ℝ≥0∞ (Set.univ : Set (Set ℕ)) where
  toFun s := s.indicator 1 0
  empty' := by simp
  sUnion' I _ hdis hmem := by
    by_cases h : 0 ∈ ⋃₀ (I : Set (Set ℕ))
    · obtain ⟨u₀, hu₀I, hu₀⟩ := h
      rw [indicator_of_mem (by exact ⟨u₀, hu₀I, hu₀⟩) 1]
      rw [Finset.sum_eq_single u₀]
      · exact (indicator_of_mem hu₀ 1).symm
      · intro b hb hne
        refine indicator_of_notMem (fun h0b ↦ ?_) 1
        exact (hdis hb hu₀I hne).notMem_of_mem_left h0b hu₀
      · intro h
        exact absurd hu₀I h
    · rw [indicator_of_notMem h 1]
      exact (Finset.sum_eq_zero fun u hu ↦
        indicator_of_notMem (fun h0u ↦ h ⟨u, hu, h0u⟩) 1).symm

@[simp]
theorem diracContent_apply (s : Set ℕ) : diracContent s = s.indicator 1 0 := rfl

/-- The Dirac content is sigma-subadditive. -/
theorem diracContent_isSigmaSubadditive : diracContent.IsSigmaSubadditive := by
  intro f _ _
  by_cases h : 0 ∈ ⋃ i, f i
  · obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.1 h
    calc diracContent (⋃ i, f i) = 1 := by simp [indicator_of_mem h]
    _ = diracContent (f i₀) := by simp [indicator_of_mem hi₀]
    _ ≤ ∑' i, diracContent (f i) := ENNReal.le_tsum i₀
  · simp [indicator_of_notMem h]

/-- The full powerset is a set semiring (via being a set ring). -/
theorem isSetSemiring_univ : IsSetSemiring (Set.univ : Set (Set ℕ)) :=
  IsSetRing.isSetSemiring ⟨trivial, fun _ _ _ _ ↦ trivial, fun _ _ _ _ ↦ trivial⟩

/-- The toy Loeb-style measure: the Dirac content extended by
`AddContent.measureCaratheodory`. -/
noncomputable def toyMeasure :=
  diracContent.measureCaratheodory isSetSemiring_univ diracContent_isSigmaSubadditive

/-- The extension property, on every set at once since the toy semiring is the full
powerset: the Carathéodory measure agrees with the content. -/
theorem toyMeasure_apply (s : Set ℕ) : toyMeasure s = s.indicator 1 0 :=
  diracContent.measureCaratheodory_eq isSetSemiring_univ diracContent_isSigmaSubadditive trivial

instance : IsProbabilityMeasure toyMeasure :=
  ⟨by rw [toyMeasure_apply]; simp⟩

/-- Completeness of the toy measure, obtained by wrapping the generic theorem — the
shape the eventual `(loebMeasure U X).IsComplete` instance must take: wrap, never
duplicate the proof. -/
instance : toyMeasure.IsComplete :=
  AddContent.measureCaratheodory_isComplete _ _ _

end Loeb
