# ADR-0003 — Loeb measure construction

Status: Accepted

Date: 2026-07-30 (proposed), 2026-07-31 (accepted)

Issue: [#3](https://github.com/cameronfreer/loeb-measure/issues/3); experiment in
[PR #8](https://github.com/cameronfreer/loeb-measure/pull/8)

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

The PR #8 spike ran option 1's route end to end on a toy content and it passed every
gate, so options 2 and 3 were not needed.

## Decision

**Carathéodory-first.** The Loeb measurable space and measure are produced by

```text
countable diagonalization ⇒ a decreasing sequence of internal sets with empty
  intersection is eventually empty, so continuity at ∅ holds outright
    → addContent_iUnion_eq_sum_of_tendsto_zero        (countable additivity)
    → isSigmaSubadditive_of_addContent_iUnion_eq_tsum (AddContent.IsSigmaSubadditive)
    → AddContent.measureCaratheodory                  (measure on the Carathéodory space)
```

The Carathéodory sigma-algebra — not the smaller `generateFrom` space — is the Loeb
measurable space. `AddContent.measure`, the `generateFrom`-trimmed variant, is
therefore explicitly **not** used: its `trim` targets the generated measurable space,
whereas the project deliberately wants the full Carathéodory space.

The internal-mod-null characterization is proved afterwards, as C7/C8, on top of this
construction.

## Consequences

- **Completeness is available generically.** The spike proved
  `AddContent.measureCaratheodory_isComplete` for any sigma-subadditive content on a
  set semiring — no finiteness or probability hypotheses — using the new four-line
  `OuterMeasure.isCaratheodory_of_measure_zero`. Since `measureCaratheodory` is
  definitionally the induced outer measure on every set, a measure-zero set is
  outer-measure-zero and hence Carathéodory measurable. The eventual
  `(loebMeasure U X).IsComplete` instance must **wrap** this generic theorem rather
  than duplicate its proof.
- **C7/C8 remain substantive approximation work** and must not be treated as formal
  consequences of the construction. In dependency order: carriers form an
  `IsSetSemiring` (I3); diagonal-driven sigma-subadditivity (C5), whose continuity at
  `∅` is supplied by M2's content-free eventual-emptiness theorem while the
  increasing-envelope form is deferred to M3 because it mentions content; unfolding
  `inducedOuterMeasure`'s infimum over countable semiring covers, which consumes
  **finite total mass** (C7); the increasing-envelope diagonal form collapsing a
  countable internal cover to a single internal set within `ε` (I6); yielding
  `exists_internal_symmDiff_lt` and `loebMeasurable_iff_internal_mod_null` (C8).
  Finite mass and saturation enter at these steps and are not concealed inside
  `measureCaratheodory`.
- **Promotion.** The two generic completeness results
  (`OuterMeasure.isCaratheodory_of_measure_zero`,
  `AddContent.measureCaratheodory_isComplete`) deserve a later isolated,
  upstream-oriented PR with minimal imports. Their final names may be bikeshedded by
  mathlib; that does not affect this decision.
- This decision determines the implementation of M3 but does not alter the stable
  downstream declarations `loebMeasurableSpace`, `loebMeasure`,
  `loebMeasure_internal`, and `loebMeasurable_iff_internal_mod_null`.
