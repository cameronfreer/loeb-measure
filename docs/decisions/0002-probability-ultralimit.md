# ADR-0002 — Probability ultralimit codomain

Status: Accepted

Date: 2026-07-30 (proposed), 2026-07-31 (accepted)

Issue: [#2](https://github.com/cameronfreer/loeb-measure/issues/2); experiment in
[PR #6](https://github.com/cameronfreer/loeb-measure/pull/6)

## Context

Internal content is the ultralimit of stagewise probability values. Mathlib provides
ultrafilter limits on nonempty compact spaces, while `AddContent` is valued in
`ℝ≥0∞`.

## Constraints

- Stagewise values are bounded between zero and one.
- Eventual equality must imply equal ultralimits.
- Finite addition on disjoint events must pass through the limit.
- Coercions into `ℝ≥0∞` must not dominate every content proof.
- The definition should not require hyperreal standard part.

## Options considered

1. The compact subtype `Set.Icc (0 : ℝ) 1`.
2. A bounded subtype of `ℝ≥0`.
3. `ℝ≥0∞` directly.
4. Hyperreal values followed by generalized standard part.

The PR #6 spike tested option 3 first and it passed every gate; the subtype options
were not needed and the hyperreal option remains a later comparison theorem only.

## Decision

Ultralimits of probability values are taken **directly in `ℝ≥0∞`**, via
`Ultrafilter.lim` applied to the pushforward ultrafilter. At the pinned revision
`ℝ≥0∞` is a compact Hausdorff order topology with continuous (unconditional)
addition, and it is already the `AddContent` codomain, so no conversion layer exists
anywhere in the content pipeline.

The accepted gate lemmas, proved in the spike with no coercion layer:
`ultralimit_const`, `ultralimit_congr`, `ultralimit_mono` (eventual and pointwise),
`ultralimit_add`, `ultralimit_le_one`, plus `ultralimit_ne_top` closing the
accidental-`∞` concern. Quotient descent to `Filter.Product` is by `Quotient.liftOn`
with representative independence supplied by `ultralimit_congr`; no canonical
representative is ever selected.

## Consequences

- `internalContent` and the integration values use `ℝ≥0∞` directly; the L1/L2
  implementation seam ([issue seeds](../issue-seeds.md)) promotes the spike's
  `Ultralimit/Compact.lean` and `Ultralimit/Probability.lean` declarations, opening
  with the M3 epic.
- **Nonemptiness is required for probability normalization (`univ` has mass one), not
  for boundedness**: on an empty stage every subset is empty and the normalized count
  is `0 / 0 = 0` in `ℝ≥0∞`, never `∞`. Nonempty-stage hypotheses therefore appear
  only on normalization statements, per the assumption-boundary rules in
  [ARCHITECTURE.md](../../ARCHITECTURE.md).
- The generic compact-ultralimit half is a mathlib upstream candidate; on upstreaming
  its declarations move to a natural namespace such as `Ultrafilter` (tracked by the
  M1 packaging unit U6).
- The hyperreal/standard-part presentation becomes a later equivalence theorem, not a
  foundation.
