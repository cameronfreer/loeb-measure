# ADR-0005 — Layout of the graded probability space bundle

Status: Accepted

Date: 2026-09-12

Issue: [#117](https://github.com/cameronfreer/loeb-measure/issues/117), probe recorded
there; epic [#116](https://github.com/cameronfreer/loeb-measure/issues/116). Deferred at
M0 as open decision 5, with the trigger *activate before M6*.

## Context

Both target programs — Elek–Szegedy realization and Hoover's relation-sampling
representation — are stated over a family of probability spaces on the finite powers
`Fin n → Ω` of one base type, related across degrees. Something must bundle that family.
What it carries as **data** and what it carries as **proof** determines whether two
bundles over the same spaces can differ, and whether the ordinary product σ-algebra can be
selected by accident.

## Constraints

- The degree-`n` measurable space is the **full Loeb σ-algebra** of the ultraproduct of
  `n`-th stage powers, transported along `Filter.Product.finPowerEquiv`. It is strictly
  larger than the ordinary product σ-algebra in general, so no instance on `Fin n → Ω`
  derived from an instance on `Ω` can be allowed to stand in for it.
- Nonemptiness is degree-specific: `Fin 0 → Ω` is a singleton whatever `Ω` is. A family of
  probability measures over an empty base cannot exist at degree one, so degree zero must be
  reachable without the bundle.
- Completeness permits arbitrary subsets of null fibers, so the sections of an arbitrary
  measurable set need not all be measurable. The bundle must not assert that they are.
- The canonical split `Fin (m + n) → Ω ≃ (Fin m → Ω) × (Fin n → Ω)` is not a measurable
  equivalence with the product of the degree-`m` and degree-`n` spaces in general, and the
  bundle must not require it to be.

## Options considered

1. **Measurable-space instances on `Fin n → Ω`.** Rejected: an instance on `Ω` already
   induces `MeasurableSpace.pi` on `Fin n → Ω`, and the two would compete.
2. **A bundle carrying measures only, with the σ-algebra recovered as the measure's
   ambient space.** Rejected: statements about measurability at a given degree would have
   no space to refer to, and mathlib's `Measure` is typed against a space in any case.
3. **Explicit degree-indexed measurable spaces, measures typed against those spaces, and
   probability as a proof.** Probed on #117: statements mentioning degrees `m`, `n` and
   `m + n` simultaneously elaborate, at the cost of `letI`/`@` at each use — the same
   discipline `loebMeasurableSpace` already imposes.

## Decision

Option 3. The bundle's **data** is

```lean
measurableSpace : ∀ n : ℕ, MeasurableSpace (Fin n → Ω)
measure : ∀ n : ℕ, @Measure (Fin n → Ω) (measurableSpace n)
```

and probability is a **proof** field. Compatibility across degrees — permutation
invariance, coordinate projections, and whatever form the split takes — is likewise
proof-valued, and its exact fields are **deferred** until P3–P8 have established the laws
they must carry. The public structure is frozen only then (P1/P9).

What is settled now and will not be revisited: no `MeasurableSpace` instances on powers;
no unconditional "every section is measurable" field; no requirement that the split be a
measurable equivalence with the product σ-algebra.

## Consequences

- P2 constructs the degree-indexed spaces and measures concretely, as `Loeb.Graded`
  definitions taking degree-specific nonemptiness, with no bundle.
- Every use site binds the degree's space explicitly. Tests state their measurable spaces,
  so none can select the product σ-algebra by accident.
- Degree zero over empty stages is available from the construction, and a test says so;
  it is not available from a bundle, and the probe shows why.
- Follow-up: the compatibility fields, once P3–P8 exist; then P1/P9.
