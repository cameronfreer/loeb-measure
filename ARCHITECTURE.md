# Architecture

This document records the project's stable architectural boundaries. Short-lived proof
plans belong in issues; unresolved foundational choices belong in
`docs/decisions/`.

## Identity and namespaces

- Repository: `loeb-measure`
- Display title: *Loeb Measure in Lean*
- Lake package: `loeb-measure`
- Lean library and root module: `LoebMeasure`
- Principal mathematical namespace: `Loeb`

Users should be able to write:

```lean
import LoebMeasure

open Loeb
```

or import a narrower module such as:

```lean
import LoebMeasure.Graded.Fubini
import LoebMeasure.Exchangeability.Hoover
```

The root module is not `Loeb`: that name is also the conventional ASCII spelling of
Löb and is already used by unrelated Lean work. The declaration namespace can remain
`Loeb` because it describes the mathematics and does not create a root-module
collision.

## Architectural invariants

### Direct ultraproducts, not a universal star framework

The carrier is mathlib's dependent quotient:

```lean
abbrev Loeb.Ultraproduct
    (U : Ultrafilter ι) (X : ι → Type*) :=
  (U : Filter ι).Product X
```

The project proves the targeted internal-set, finite-power, and diagonalization facts
it needs directly. First-order Łoś can be connected later, but it is not a dependency
of Loeb measurability or Fubini.

### Graded finite powers are primary

For each `n`, the measure is constructed from internal subsets of
`Product U (fun i => Fin n → X i)`, then transported to
`Fin n → Product U X`. The resulting measurable space may be strictly larger than the
ordinary product measurable space generated from degree one.

Consequently:

- never define the degree-`n` Loeb measure as an `n`-fold product of the degree-one
  measure;
- never use equality with a product sigma-algebra as a Fubini goal;
- state section and Fubini theorems for the larger degree-`m+n` measurable space.

### Quotient data and interpreted sets stay separate

An internal set is quotient data represented by a family `A i : Set (X i)`. Its
`carrier` is an actual subset of the ultraproduct. The two should not be definitionally
identified.

This separation keeps:

- quotient equality and set extensionality distinct;
- representative proofs localized;
- Boolean operations computational on internal data; and
- downstream measure theory phrased in ordinary `Set` and `MeasurableSet` language.

### Probability ultralimits are bounded topological limits in `ℝ≥0∞`

Stagewise probabilities are combined by an ultrafilter limit, never by a detour through
hyperreals and standard part. The codomain is `ℝ≥0∞` directly: it is compact Hausdorff
with continuous addition and is already the `AddContent` codomain, so no conversion
layer appears in the content pipeline (ADR-0002). Nonemptiness of the stage spaces is
required for probability *normalization*, not for boundedness.

### The first concrete model is normalized finite counting measure

The initial Loeb construction targets nonempty finite types with normalized counting
measure. General families of probability spaces are an intended extension, but are not
allowed to complicate the first construction unless a design spike shows the general
API is no harder.

### Generic helpers use mathlib namespaces

Genuinely generic improvements to `Filter.Product`, finite powers, `AddContent`, or
measure theory use their natural namespaces and avoid `Loeb` in declaration names.
Loeb-specific contents, measurable spaces, graded structures, and applications live
under `Loeb`.

Potential upstream declarations should be isolated in modules whose dependency set is
acceptable to mathlib.

## Module layers

Modules are grouped into dependency layers under `LoebMeasure/`. The layers, not the
individual files, are the architectural commitment; a file inventory would age with
every merge, so the module docstrings are the reference for what exists.

Within a layer, a module imports only what it uses; the root `LoebMeasure.lean` is the
umbrella that exposes the whole public surface. In particular the ultraproduct layer is
not a chain — `FinitePower` does not depend on `Prod`:

```text
Basic → Map → Prod
            ↘ FinitePower → Permutation
```

```text
Ultraproduct/   the generic dependent filter-product API
Internal/       internal sets, functions, relations, and diagonalization
Ultralimit/     compact ultralimits and probability values
Measure/        internal content, Loeb measure, approximation, completion
Integral/       bounded internal functions and their integrals
Graded/         graded finite powers, sections, and Fubini
GraphLimit/     internal graphs, homomorphism densities, graphon realization
Exchangeability/  relation sampling and the Hoover representation
Hypergraph/     coordinate systems, total independence, Elek–Szegedy
```

Directories are dependency layers, not mandatory namespace components. For example:

```text
file:      LoebMeasure/Exchangeability/Hoover.lean
namespace: Loeb.Exchangeability

file:      LoebMeasure/Hypergraph/ElekSzegedy.lean
namespace: Loeb.Hypergraph
```

Author names belong in filenames and theorem documentation. Primary declaration names
should be indexed by mathematical content.

## Dependency direction

```text
Mathlib
  ↓
Ultraproduct
  ↓
Internal ───────────────┐
  ↓                     │
Ultralimit              │
  ↓                     │
Measure                 │
  ├──→ GraphLimit/HomDensity
  ↓
Integral
  ↓
Graded
  ├──→ Exchangeability
  ├──→ GraphLimit/GraphonRealization
  └──→ Hypergraph
```

Application modules must not be imported by the common foundation. The root
`LoebMeasure.lean` may import completed public modules, but it is not used to break
cycles.

## Mathematical assumption boundaries

The API should make these assumptions visible:

- nonempty fibers, where representative selection needs them;
- ultrafilter versus arbitrary filter;
- freeness or countable incompleteness, only where diagonalization needs it;
- finite nonempty stage spaces for normalized counting;
- uniformly bounded functions for the first integration theory;
- growing stage cardinalities only for atomlessness; and
- symmetry/exchangeability only in application modules.

In particular, “free ultrafilter” must not be an undocumented global convention.

## Public API rules

- Prefer `Fin n → Ω` for finite powers.
- Use the single canonical coordinate split `Loeb.splitEquiv` (wrapping mathlib's
  `Fin.appendEquiv`), kept opaque so downstream code depends on its wrapper simp
  lemmas rather than on the underlying equivalence. Never introduce a competing split.
- The permutation action on finite powers is a contravariant pullback:
  `permute (σ * τ) = permute τ ∘ permute σ`, not the covariant `MulAction` convention.
- Give coordinate maps and equivalences named simp lemmas.
- Downstream proofs should not use `Quotient.sound` directly.
- Avoid global `MeasurableSpace` instances when multiple degrees or transported
  measurable spaces can coexist; use explicit measures/spaces or scoped/local
  instances.
- Provide both set and bounded-function forms of section/Fubini results.
- Keep the `n = 0` case in the core API and prove convenience lemmas so later theorems
  do not repeatedly split it.
- Root imports expose only completed, documented modules.

## Decisions

Choices whose consequences span milestones are recorded as decision records rather than
buried in an implementation PR. The accepted decisions are already incorporated above as
invariants; [docs/decisions/README.md](docs/decisions/README.md) owns their status list.

Two decisions are deliberately deferred, with their activation triggers:

- whether general probability spaces cost essentially more than finite counting spaces
  — activate before M3;
- what `Graded.ProbabilitySpace` bundles — measurable spaces, measures, or both with
  explicit compatibility proofs — activate before M6.

See [docs/decisions/README.md](docs/decisions/README.md).
