# ADR-0003 — Loeb measure construction

Status: Proposed

Date: 2026-07-30

Issue: not yet created

## Context

Mathlib can extend a sigma-subadditive `MeasureTheory.AddContent` on a set semiring by
Carathéodory. Elek–Szegedy instead present the measurable sets directly as sets that
are internal modulo a sigma-ideal of null sets.

Downstream work needs both:

- a standard `MeasurableSpace`/`Measure` compatible with mathlib integration; and
- the internal-mod-null characterization used throughout the paper.

## Constraints

- Internal carriers form a Boolean algebra/set ring.
- The constructed measure must agree with internal content.
- Completeness and null-cover lemmas must be ergonomic.
- The two presentations should not drift into competing measurable spaces.

## Options considered

1. Define the Carathéodory measure first, then prove the internal-mod-null
   characterization.
2. Define the internal-mod-null sigma-algebra and measure directly.
3. Construct both and prove equality early.

## Candidate mathlib route

The currently preferred implementation path at the pinned revision is:

1. countable diagonalization makes a decreasing sequence of internal sets with empty
   intersection *eventually empty*, giving continuity at `∅` outright;
2. `addContent_iUnion_eq_sum_of_tendsto_zero` upgrades continuity at `∅` to countable
   additivity on the internal set ring;
3. `isSigmaSubadditive_of_addContent_iUnion_eq_tsum` supplies
   `AddContent.IsSigmaSubadditive`;
4. `AddContent.measureCaratheodory` produces the measure on the Carathéodory
   measurable space.

Two consequences are **not** automatic and remain substantive theorems:

- completeness: a `Measure.IsComplete` instance needs a short direct proof from the
  Carathéodory construction, it is not supplied by the API;
- `loebMeasurable_iff_internal_mod_null` is a genuine approximation theorem using
  finite total mass and the diagonal lemma, not a formal consequence of the
  construction.

## Provisional direction

Start with `AddContent.measureCaratheodory` along the route above if a toy
construction shows that its measurable space and completion API lead cleanly to the
Elek–Szegedy characterization. Otherwise define the paper's completion directly and
prove its equivalence to the Carathéodory presentation.

## Consequences

This decision determines the implementation of M3 but should not alter the stable
downstream declarations `loebMeasurableSpace`, `loebMeasure`,
`loebMeasure_internal`, and `loebMeasurable_iff_internal_mod_null`.
