# ADR-0003 — Loeb measure construction

Status: Proposed

Date: 2026-07-30

Issue: not yet created

## Context

Mathlib can extend a sigma-subadditive `MeasureTheory.AddContent` on a set semiring by
Carathéodory. Elek--Szegedy instead present the measurable sets directly as sets that
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

## Provisional direction

Start with `AddContent.measureCaratheodory` if a toy construction shows that its
measurable space and completion API lead cleanly to the Elek--Szegedy
characterization. Otherwise define the paper's completion directly and prove its
equivalence to the Carathéodory presentation.

## Consequences

This decision determines the implementation of M3 but should not alter the stable
downstream declarations `loebMeasurableSpace`, `loebMeasure`,
`loebMeasure_internal`, and `loebMeasurable_iff_internal_mod_null`.
