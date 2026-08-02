# Loeb Measure in Lean

[![Lean Action CI](https://github.com/cameronfreer/loeb-measure/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/cameronfreer/loeb-measure/actions/workflows/lean_action_ci.yml)

Loeb measure, ultraproduct probability, and applications to exchangeability and graph
limits, in Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4).

The project is deliberately narrower than a general nonstandard-analysis framework. Its
goal is a reusable library for dependent ultraproducts, internal sets and bounded
functions, Loeb measure and integration, and the **graded** finite-power/Fubini theory
needed by Hoover and Elek–Szegedy. A universal star map, automatic transfer, and
hyperreal calculus are not dependencies.

## Where the project is

A reusable API over mathlib's dependent filter product is in place under
`LoebMeasure/Ultraproduct/`; the foundational design decisions behind it are settled and
recorded in [`docs/decisions/`](docs/decisions). Loeb measure itself is not built yet.

The current milestone, its gate, and everything still to come are in the
[roadmap](ROADMAP.md); open work is on the issue tracker. This section is deliberately
coarse so that it stays true — treat the roadmap and the issues as the live record.

## Using it

```lean
import LoebMeasure

open Loeb

#check Ultraproduct   -- an ultrafilter-indexed dependent filter product
```

Project-specific declarations live in the `Loeb` namespace. Generic results instead use
the natural mathlib namespace they belong to — the ultraproduct API is stated for
`Filter.Product` and applies to `Loeb.Ultraproduct` without restatement. That split is
what keeps the generic half upstreamable, and it is a rule rather than an accident: see
[ARCHITECTURE](ARCHITECTURE.md).

Each module's docstring states its own contents and conventions; that is the reference
for what exists, in preference to any list kept here.

## The mathematical plan

```text
dependent ultraproduct API
        ↓
internal sets + countable diagonalization
        ↓
bounded ultralimits + internal content
        ↓
Loeb measure + internal approximation
        ↓
bounded internal integration
        ↓
graded finite powers, sections, and Fubini
        ↓
        ├── Hoover relation-sampling representation
        └── Elek–Szegedy coordinate factors and graphon realization
```

Two commitments shape everything below that line. The finite-power spaces are
**graded**: the Loeb measurable space on an ultraproduct of finite powers is not
replaced by the generally smaller ordinary product measurable space. And the first
end-to-end application is the homomorphism-density identity for an internal graph,
which exercises the ultraproduct, internal-set, finite-power, and Loeb-measure APIs
before the much harder Fubini and realization work.

## Building

The project pins Lean `v4.32.2` and the mathlib revision at that tag
(`905b95818eb32af7874a58b427f50c1711a5e96c`), so it builds against exactly one mathlib.

```bash
lake exe cache get   # mathlib build cache
lake build
```

## Project guides

- [Roadmap](ROADMAP.md) — milestone gates and the two application branches.
- [Architecture](ARCHITECTURE.md) — stable naming, namespace, and dependency rules.
- [Decisions](docs/decisions) — accepted records for the foundational choices.
- [Declaration blueprint](docs/blueprint.md) — planned Lean API and its dependency DAG.
- [Contributing](CONTRIBUTING.md) — proof and review workflow.
- [Tracking guide](docs/tracking.md) — milestones, labels, and what "done" means.
- [Issue seeds](docs/issue-seeds.md) — epics and work units not yet opened.
- [Research landscape](docs/research-landscape.md) — prover/library survey and sources.

## License

Apache-2.0. See [LICENSE](LICENSE).
