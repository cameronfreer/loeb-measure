# Documentation map

Each document below owns one responsibility. Keeping that division sharp is what stops
any single file from turning into a changelog or a project dashboard.

| Location | Responsibility |
| --- | --- |
| [README](../README.md) | Purpose, usable surface, coarse status, quick start |
| [ROADMAP](../ROADMAP.md) | Capability sequence and mathematical gates |
| [ARCHITECTURE](../ARCHITECTURE.md) | Stable invariants and dependency boundaries |
| [decisions/](decisions) | Why foundational choices were made |
| GitHub milestones and issues | Live status and work history |
| Module docstrings | The actual API reference |
| [CONTRIBUTING](../CONTRIBUTING.md), [tracking](tracking.md) | Development process |

Two consequences worth stating explicitly, because they are easy to violate one commit
at a time:

- **Status lives on GitHub, not in files.** Milestones and issues are the live record.
  Prose in the repository should describe capabilities and invariants, not progress.
- **A closed gate closes its milestone.** When a milestone's roadmap gate is met, close
  the GitHub milestone and move any unresolved non-gating follow-ups elsewhere — an
  upstreaming bucket, or a later milestone. Leaving nonblocking work attached makes a
  finished milestone look unfinished.
- **The API reference is the module docstrings.** Not because docstrings cannot drift —
  review has caught them drifting — but because they are reviewed alongside the
  declarations they describe, so they drift far less than a duplicated inventory kept
  somewhere else.

## What does not belong in the README

No exact counts, exhaustive file trees, per-merge history, duplicated version pins, or
long proof narratives. Each of those has to be maintained by hand and drifts silently;
each has a better home in this map.

## The documents

### Planning and design

- [ROADMAP](../ROADMAP.md) — milestones M0–M10, each ending in a compiled capability,
  with the gate that closes it. Dependency-driven rather than calendar-driven.
- [ARCHITECTURE](../ARCHITECTURE.md) — naming, namespaces, module layering, and the
  invariants that must not be violated (in particular that finite powers are graded).
- [decisions/](decisions) — architecture decision records for choices whose
  consequences span milestones, plus the ones deliberately deferred until their
  milestone reaches them.
- [blueprint](blueprint.md) — declaration-level sketches and the dependency DAG for
  layers not yet implemented. Superseded by the code wherever the code exists.

### Background

- [research-landscape](research-landscape.md) — what nonstandard analysis exists in
  Lean and in other provers, what is missing, and the primary sources for the two
  target papers. Date-stamped; re-audit when the mathlib pin changes.

### Process

- [CONTRIBUTING](../CONTRIBUTING.md) — proof and review workflow, Lean style, and the
  definition of done.
- [tracking](tracking.md) — milestone/label vocabulary and the criteria for an issue
  being ready or done.
- [issue-seeds](issue-seeds.md) — the original work-unit decomposition. A historical
  planning record, **not** updated as issues open or close; GitHub is authoritative,
  and a remaining seed should be revalidated before it is opened.

### Upstreaming

Generic material intended for mathlib is kept under a
[`LoebMeasure/Mathlib/`](../LoebMeasure/Mathlib/README.md) mirror directory whose paths
match the proposed upstream module. Its README records the convention, and
[ARCHITECTURE](../ARCHITECTURE.md) records it as an architectural rule.
