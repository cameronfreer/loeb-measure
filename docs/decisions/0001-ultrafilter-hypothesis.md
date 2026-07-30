# ADR-0001 — Ultrafilter hypothesis

Status: Proposed

Date: 2026-07-30

Issue: [#1](https://github.com/cameronfreer/loeb-measure/issues/1)

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

## Provisional direction

Keep M1 and the elementary part of M2 generic in a filter or ultrafilter. Test a small
project predicate for countable incompleteness in the M0 spike, with a theorem or
instance showing that `Filter.hyperfilter ℕ` satisfies it.

No option is accepted until the content-free diagonal statement elaborates.

## Consequences

This decision controls all saturation/diagonal assumptions and the generality of the
measure constructor. Downstream issues remain blocked until it is accepted.
