# Architecture decision records

Decision records preserve foundational choices whose consequences span several
milestones. They are short and should link to an issue containing experiments and
discussion.

Status values:

- Proposed
- Accepted
- Superseded
- Rejected

Create a record from this template:

```markdown
# ADR-NNNN — Decision title

Status: Proposed
Date: YYYY-MM-DD
Issue: #…

## Context

What mathematical/API choice is required?

## Constraints

Which theorems, mathlib APIs, and assumptions constrain it?

## Options considered

List concrete alternatives and experiment results.

## Decision

State the selected option and its exact scope.

## Consequences

Record benefits, costs, follow-up issues, and migration risks.
```

Accepted records:

- [ADR-0001: ultrafilter hypothesis](0001-ultrafilter-hypothesis.md) — countable
  incompleteness as a predicate on `Filter`.
- [ADR-0002: probability ultralimit codomain](0002-probability-ultralimit.md) — `ℝ≥0∞`
  directly.
- [ADR-0003: Loeb measure construction](0003-loeb-measure-construction.md) —
  Carathéodory-first.

Anticipated records, deliberately not created yet so unstable work is not seeded
prematurely:

- general versus counting-space construction — activate before M3 implementation
  starts;
- contents of `Graded.ProbabilitySpace` — activate before M6 implementation starts.

These correspond to open decisions 4 and 5 in [ARCHITECTURE.md](../../ARCHITECTURE.md);
they receive ADR numbers when activated.
