# Tracking guide

The tracking system is designed to show mathematical dependencies, not just activity.

## Hierarchy

Use four levels:

1. `ROADMAP.md` records the durable program and milestone gates.
2. One GitHub milestone corresponds to each roadmap milestone.
3. One epic issue owns each coherent mathematical capability.
4. Work-unit issues add a small compiling seam and link their blockers.

Do not duplicate the full roadmap in a GitHub project description. The project board is
an operational view of the issue graph.

## Recommended project board

Create one repository project named **Loeb Measure development** with:

- Status: Backlog, Ready, In progress, In review, Blocked, Done
- Milestone
- Area
- Kind
- Effort: S, M, L, XL
- Upstream candidate: yes/no

Use GitHub's blocked-by/sub-issue relationships for the actual dependency graph.
“Blocked” means a named issue or decision is unresolved, not merely that a proof is
difficult.

## Labels

Keep labels orthogonal so they can be combined.

Create the label set in the repository before publishing the issue forms: GitHub
silently drops labels that do not yet exist when a form is submitted.

### Area

- `area: ultraproduct`
- `area: internal`
- `area: ultralimit`
- `area: measure`
- `area: integral`
- `area: graded`
- `area: graph-limit`
- `area: exchangeability`
- `area: hypergraph`
- `area: infrastructure`

### Kind

- `kind: research`
- `kind: design`
- `kind: definition`
- `kind: theorem`
- `kind: documentation`
- `kind: upstream`

### Difficulty and onboarding

- `difficulty: small`
- `difficulty: medium`
- `difficulty: hard`
- `difficulty: research`
- `good first issue`
- `help wanted`

Avoid priority labels unless two ready issues in the same milestone genuinely compete.
The dependency order already supplies most prioritization.

## Issue states

An issue is **Ready** only when:

- every blocker is closed;
- its target module and declaration seam are named;
- assumptions are explicit;
- acceptance criteria can be checked by a reviewer; and
- no unresolved architecture choice is buried in the task.

An issue is **Done** only when:

- the merged code builds without `sorry`;
- the public API has docstrings and examples/simp lemmas where appropriate;
- its acceptance criteria are met;
- dependent issue descriptions still have correct assumptions; and
- any resulting design choice is recorded.

## Research spikes and decisions

Research issues are time-bounded and must produce:

1. a small elaborating experiment or a precise source/API audit;
2. alternatives and tradeoffs;
3. a recommendation;
4. an accepted decision record in `docs/decisions/`; and
5. follow-up implementation issues.

A spike does not close with “more research needed.” It either narrows the next
experiment or records the specific blocker.

## Epic issue format

An epic should include:

- mathematical outcome;
- out-of-scope items;
- source theorem(s);
- child issues;
- dependency list;
- public API expected at the gate; and
- a checkbox for updating the roadmap/blueprint.

The epic closes only when its roadmap gate is met.

## Work-unit issue format

Each work unit should state:

- target module;
- candidate declarations;
- mathematical assumptions;
- blockers;
- proof/source notes;
- acceptance criteria;
- upstream destination, if any.

The repository's issue forms prompt for these fields.

## Suggested initial issue creation

Create issues in this order:

1. M0 epic and the four initial spikes (D0.1–D0.4).
2. M1 epic and only its first representative/map work units.
3. M2 and M3 epics as visible future work, with their units left blocked.
4. M4 vertical-slice epic so the first application target is visible.
5. M5–M10 as roadmap entries; create detailed issues only as their assumptions become
   stable.

This avoids a backlog of dozens of stale theorem signatures.

The full seed list in [issue-seeds.md](issue-seeds.md) is intentionally more detailed
than the set that should be opened on day one.

## Progress reporting

Report progress by gates and public capabilities:

- “finite-power equivalence merged”;
- “internal carriers form a set ring”;
- “Loeb measure agrees with internal content”;
- “graded Fubini complete.”

Counts of files, lines, or closed issues are secondary and should not be used as the
main completion metric.
