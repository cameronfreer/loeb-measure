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

### Probability ultralimits are bounded topological limits

Stagewise probabilities lie in a compact bounded range. The foundational definition
should use an ultrafilter limit in that range, rather than detouring through hyperreals
and standard part. The precise codomain is an M0 decision because it affects continuity
and coercion proofs.

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

## Planned module tree

```text
LoebMeasure.lean

LoebMeasure/
  Ultraproduct/
    Basic.lean
    Map.lean
    FinitePower.lean
    Permutation.lean

  Internal/
    Set.lean
    Function.lean
    Relation.lean
    Diagonal.lean

  Ultralimit/
    Compact.lean
    Probability.lean

  Measure/
    Content.lean
    Construction.lean
    Approximation.lean
    Completion.lean

  Integral/
    Bounded.lean
    InternalFunction.lean

  Graded/
    Basic.lean
    Power.lean
    Section.lean
    Fubini.lean
    CoordinateSigma.lean

  Exchangeability/
    Sampling.lean
    Hoover.lean

  GraphLimit/
    InternalGraph.lean
    HomDensity.lean
    GraphonRealization.lean

  Hypergraph/
    CoordinateSigma.lean
    TotalIndependence.lean
    ElekSzegedy.lean
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

## Open decisions

The following decisions are intentionally not hidden inside the first implementation
PR:

1. the exact property expressing freeness/countable incompleteness;
2. the compact codomain for probability ultralimits;
3. the precise `AddContent`/Carathéodory construction and its relation to the
   Elek–Szegedy null-completion definition;
4. whether general probability spaces cost essentially more than finite counting
   spaces at M3; and
5. whether `Graded.ProbabilitySpace` bundles measurable spaces, measures, or both with
   explicit compatibility proofs.

See [docs/decisions/README.md](docs/decisions/README.md).
