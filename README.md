# Loeb Measure in Lean

[![Lean Action CI](https://github.com/cameronfreer/loeb-measure/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/cameronfreer/loeb-measure/actions/workflows/lean_action_ci.yml)

Loeb measure, ultraproduct probability, and applications to exchangeability and graph
limits, in Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4).

The project is deliberately narrower than a general nonstandard-analysis framework. Its
goal is a reusable library for dependent ultraproducts, internal sets and bounded
functions, Loeb measure and integration, and the **graded** finite-power/Fubini theory
needed by Hoover and Elek–Szegedy. The core Loeb construction does not require a
universal star map, automatic transfer, or hyperreal calculus.

## Status

This project is under active development. The Loeb measure construction and its
applications are still in progress.

| Layer | Available now | Next boundary |
| --- | --- | --- |
| Dependent ultraproducts | Representatives and eliminators; coordinatewise maps; binary and finite-power equivalences; reindexing and permutations | — |
| Internal sets | Faithful carriers; Boolean algebra and the realized set ring; internal maps, preimages, and relations; countable saturation | Internal content and Loeb measure |

The [roadmap](ROADMAP.md) describes the capability sequence; GitHub milestones and
issues are the live development record.

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

## Trust

CI builds the public library against the pinned Lean/mathlib environment with warnings
treated as errors, which also rejects `sorry`. It additionally runs an axiom audit:
every **audited boundary declaration** — selected public entry points from each module,
listed in `scripts/AxiomAudit.lean` — must depend only on `propext`, `Classical.choice`, and
`Quot.sound`, transitively. That is a boundary audit, not an enumeration of every
declaration in the library.

## Building

Lean and mathlib versions are pinned by `lean-toolchain` and `lake-manifest.json`, so
the project builds against exactly one mathlib.

```bash
lake exe cache get   # mathlib build cache
lake build
```

## Further reading

- [Roadmap](ROADMAP.md) — the capability sequence and its mathematical gates.
- [Architecture](ARCHITECTURE.md) and the [decision records](docs/decisions) — stable
  invariants, and why the foundational choices were made.
- [Research landscape](docs/research-landscape.md) — what exists in Lean and other
  provers, and the primary sources.
- [Contributing](CONTRIBUTING.md) — proof and review workflow.

A full map of the project's documentation is in [docs/README.md](docs/README.md).

## License

Apache-2.0. See [LICENSE](LICENSE).
