# Loeb Measure in Lean

[![Lean Action CI](https://github.com/cameronfreer/loeb-measure/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/cameronfreer/loeb-measure/actions/workflows/lean_action_ci.yml)

Loeb measure, ultraproduct probability, and applications to exchangeability and graph
limits, in Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4).

The project is deliberately narrower than a general nonstandard-analysis framework. Its
first goal is a reusable library for dependent ultraproducts, internal sets and bounded
functions, Loeb measure and integration, and the **graded** finite-power/Fubini theory
needed by Hoover and Elek–Szegedy.

**Status.** The M0 design spikes are complete and their three decision records are
accepted. Milestone M1 — an ergonomic API over mathlib's dependent filter product — is
implemented: representatives and eliminators, coordinatewise maps, the binary product
equivalence, the finite dependent-product and `Fin`-power equivalences, and coordinate
reindexing with the permutation action. Internal sets, content, and Loeb measure (M2
and M3) have not landed yet.

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
LoebMeasure.lean                           root import spine
LoebMeasure/Basic.lean                     the project-facing `Loeb` surface
LoebMeasure/Ultraproduct/Basic.lean        representatives, eliminators, liftOn
LoebMeasure/Ultraproduct/Map.lean          coordinatewise maps and functor laws
LoebMeasure/Ultraproduct/Prod.lean         the binary product equivalence
LoebMeasure/Ultraproduct/FinitePower.lean  finite dependent-product / `Fin`-power equivalences
LoebMeasure/Ultraproduct/Permutation.lean  coordinate reindexing and the permutation action
docs/                                      design, tracking, and research guides
```

Project-facing declarations live in the `Loeb` namespace:

```lean
import LoebMeasure

open Loeb

#check Ultraproduct   -- an ultrafilter-indexed dependent filter product
```

Generic extensions of existing mathlib objects instead use their natural mathlib
namespace: the whole M1 layer is stated for `Filter.Product` and applies to
`Loeb.Ultraproduct` without restatement, which is what keeps it upstreamable.

## License

Apache-2.0. See [LICENSE](LICENSE).
