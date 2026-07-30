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

Prefer a compact Hausdorff bounded probability type and convert once at the
`AddContent` boundary. The M0 spike must test continuity of every operation needed for
finite additivity before selecting the concrete type.

## Consequences

The choice affects `internalContent`, finite-additivity proofs, integration values, and
the public ultralimit API. It should be settled before those declarations stabilize.
