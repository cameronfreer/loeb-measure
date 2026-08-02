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
- **The API reference is the module docstrings.** Lists of declarations or files kept
  elsewhere go stale independently of the code; docstrings cannot.

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
- [issue-seeds](issue-seeds.md) — planned epics and work units that have not been
  opened yet. Entries are removed as they become real issues.

### Upstreaming

Generic material intended for mathlib is kept under a `LoebMeasure/Mathlib/` mirror
directory whose paths match the proposed upstream module, with its own README recording
the convention. That directory currently exists only on the M0 spike branches; it
reaches `main` when the first upstream-shaped material is promoted.
