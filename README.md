# Loeb Measure in Lean

[![Lean Action CI](https://github.com/cameronfreer/loeb-measure/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/cameronfreer/loeb-measure/actions/workflows/lean_action_ci.yml)

Loeb measure, ultraproduct probability, and applications to exchangeability and graph
limits, in Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4).

The project is deliberately narrower than a general nonstandard-analysis framework. Its
first goal is a reusable library for dependent ultraproducts, internal sets and bounded
functions, Loeb measure and integration, and the **graded** finite-power/Fubini theory
needed by Hoover and Elek–Szegedy.

The repository is currently a scaffold: the build, root import spine, and CI are wired
up, but the mathematical content has not landed yet.

## Scope

The common critical path is:

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

The finite-power spaces are graded: the Loeb measurable space on an ultraproduct
of finite powers is not replaced by the generally smaller ordinary product
measurable space. A universal star map, automatic transfer, hyperreal calculus, and
the full structure/uniqueness theories of either target are not initial dependencies.

The first end-to-end application will be the homomorphism-density identity for an
internal graph. It gives an early test of the ultraproduct, internal-set, finite-power,
and Loeb-measure APIs before the much harder Fubini and realization work.

## Project guides

- [Roadmap](ROADMAP.md) gives milestone gates and the two application branches.
- [Architecture](ARCHITECTURE.md) records stable naming and dependency rules.
- [Declaration blueprint](docs/blueprint.md) sketches the initial Lean API and its DAG.
- [Issue seeds](docs/issue-seeds.md) lists ready-to-create epics and work units.
- [Tracking guide](docs/tracking.md) defines milestones, labels, and “done.”
- [Research landscape](docs/research-landscape.md) records the current prover/library
  survey and primary references.
- [Contributing](CONTRIBUTING.md) describes the proof and review workflow.

## Building

The project pins Lean `v4.32.2` and the mathlib revision at that tag
(`905b95818eb32af7874a58b427f50c1711a5e96c`), so it builds against exactly one mathlib.

```bash
lake exe cache get   # mathlib build cache
lake build
```

## Layout

```
LoebMeasure.lean         root import spine
LoebMeasure/Basic.lean   temporary scaffold
docs/                    design, tracking, and research guides
```

Declarations live principally in the `Loeb` namespace:

```lean
import LoebMeasure

open Loeb
```

Generic extensions of existing mathlib objects instead use their natural mathlib
namespace, for example `Filter.Product`.

## License

Apache-2.0. See [LICENSE](LICENSE).
