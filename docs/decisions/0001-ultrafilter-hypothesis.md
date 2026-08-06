# ADR-0001 — Ultrafilter hypothesis

Status: Accepted

Date: 2026-07-30 (proposed), 2026-07-31 (accepted)

Issue: [#1](https://github.com/cameronfreer/loeb-measure/issues/1); experiment in
[PR #7](https://github.com/cameronfreer/loeb-measure/pull/7)

## Context

Algebraic ultraproduct and internal-set operations work for broad filters. The
countable diagonalization used by Loeb measure needs more: the intended applications
use a nonprincipal ultrafilter on `ℕ`, while reusable statements may be better phrased
through countable incompleteness.

## Constraints

- The canonical `Filter.hyperfilter ℕ` must be supported.
- Freeness must not be a hidden convention.
- The measure layer needs exactly the hypothesis used by its diagonal lemma.
- Generic `Filter.Product` helpers should not acquire unnecessary ultrafilter
  assumptions.

## Options considered

1. Fix `Filter.hyperfilter ℕ` throughout.
2. Parameterize by a nonprincipal `U : Ultrafilter ℕ`.
3. Define a predicate expressing countable incompleteness and parameterize the
   diagonal layer by it.
4. Generalize further to arbitrary index types equipped with a suitable decreasing
   family or rank.

The PR #7 spike proved the full diagonal lemma under option 3 and refined it: the
predicate and the lemma naturally live on `Filter`, not `Ultrafilter`.

## Decision

The diagonal layer is parameterized by

```lean
Filter.CountablyIncomplete (F : Filter ι) : Prop
-- some countable family of members of F has empty intersection
```

— option 3, refined to the `Filter` level. The content-free diagonal lemma
(`CountablyIncomplete.exists_forall_eventually_mem`) is proved from this hypothesis
alone plus nonempty fibers for choosing a stagewise witness or default value; **no
ultrafilter property is consumed by the diagonalization**.
M1 and the elementary part of M2 stay generic in a filter or ultrafilter; only the
diagonal layer takes the predicate.

Coverage of the concrete applications: `countablyIncomplete_of_le_cofinite` shows any
filter refining `cofinite` on a countable index type qualifies — in particular every
nonprincipal ultrafilter on `ℕ` — and `hyperfilter_countablyIncomplete` records the
canonical instance.

## Consequences

- **Properness is separate.** `CountablyIncomplete` does not include `Filter.NeBot`;
  the bottom filter satisfies it vacuously (and its diagonal conclusion is trivial).
  This is harmless and gives the weakest operational diagonal hypothesis; properness
  is supplied automatically by the eventual `Ultrafilter` in applications. Promotion
  of the generic predicate should revisit its final name and properness convention.
- **Where the ultrafilter genuinely enters — at M2, not the diagonal layer.** With
  nonempty fibers, `carrier(A).Nonempty ↔ ∀ᶠ i in F, (A i).Nonempty` holds for *any*
  filter. The ultrafilter dichotomy is needed to pass from the quotient-level
  inequality `A ≠ InternalSet.empty` to eventual nonemptiness (quotient equality only
  gives `A = empty ↔ ∀ᶠ i, A i = ∅`), and for carrier injectivity. Neither uses
  countable incompleteness. The M2 issues (I2, I5, I6) must keep these hypotheses
  separated exactly this way.
- Downstream units I5/I6/C5 consume the named diagonal API
  (`exists_forall_eventually_mem` and its antitone corollary) rather than re-proving
  ad hoc diagonal arguments.
- The predicate and diagonal lemma are mathlib upstream candidates in the `Filter`
  namespace (tracked by the M1 packaging unit U6).
