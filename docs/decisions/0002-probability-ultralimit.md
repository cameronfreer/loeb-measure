# ADR-0002 — Probability ultralimit codomain

Status: Proposed

Date: 2026-07-30

Issue: not yet created

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
3. `ℝ≥0∞` or its unit interval directly.
4. Hyperreal values followed by generalized standard part.

## Provisional direction

Prefer `ℝ≥0∞` directly. At the pinned revision it is a compact Hausdorff order
topology with continuous bounded addition, and it is already the `AddContent`
codomain, so no conversion layer is needed at all. The M0 spike must still verify the
constant, congruence, order-bound, and finite-additivity lemmas in `ℝ≥0∞`, and should
keep a bounded compact subtype as the fallback if `ℝ≥0∞` arithmetic turns out to
dominate the content proofs. Before acceptance the spike must establish at least:

```text
ultralimit_const
ultralimit_congr
ultralimit_mono
ultralimit_add
ultralimit_le_one
```

in the chosen codomain. Hyperreal standard part remains a later comparison theorem
only.

## Consequences

The choice affects `internalContent`, finite-additivity proofs, integration values, and
the public ultralimit API. It should be settled before those declarations stabilize.
