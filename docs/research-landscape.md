# Research landscape

Last audited: **2026-07-30**, against the repository's pinned mathlib revision
`905b95818eb32af7874a58b427f50c1711a5e96c` (Lean `v4.32.2`).

This is a planning survey, not a claim that every external repository has been
exhaustively reviewed. Re-audit it when the mathlib pin changes or before adopting an
external nonstandard-analysis dependency.

## The two target sources

### Hoover

Douglas Hoover's *Relations on Probability Spaces and Arrays of Random Variables*
uses ultraproducts, Loeb extension, and a family of finite-power probability spaces
with a Fubini property to obtain relation-sampling representations. Its later
structure theory adds lower-support sigma-algebras, relative atomlessness, independent
uniform coordinates, and measure-algebraic equivalence.

Primary source:
[Hoover manuscript](https://www.stat.berkeley.edu/~aldous/Research/hoover.pdf).

The roadmap calls the nonstandard graded relation-sampling result **Hoover I**. The
usual latent-uniform Aldous--Hoover representation and the full uniqueness theory are
separate later projects.

### Elek--Szegedy

Elek and Szegedy construct a Loeb probability space from ultraproducts of finite
counting spaces, define coordinate sigma-algebras, prove Total Independence, and use
separable realizations to move to Euclidean hypergraphons. Their construction defines
measurable sets as internal modulo a sigma-ideal of null sets, and their bounded
internal functions satisfy an ultralimit integral formula.

Primary source:
[Elek--Szegedy, *A measure-theoretic approach to the theory of dense
hypergraphs*](https://arxiv.org/pdf/0810.4062).

The graph case is much smaller than the uniform-`k` development and is the first
realization target.

## What pinned mathlib already provides

| Component | Status | Relevant source |
| --- | --- | --- |
| Germs modulo eventual equality | Present | [`Filter.Germ`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Germ/Basic.html) |
| Dependent filter product quotient | Present, with a very small direct API | [`Filter.Product`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/FilterProduct.html) and `Germ.Basic` |
| Algebraic structures on germs at an ultrafilter | Present | [`FilterProduct`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/FilterProduct.html) |
| First-order ultraproduct structures and Łoś | Present | [`ModelTheory.Ultraproducts`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Ultraproducts.html) |
| A canonical free ultrafilter extending cofinite | Present as `Filter.hyperfilter` | [`Ultrafilter.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Ultrafilter/Basic.html) |
| Ultrafilter limits in compact spaces | Present | [`Topology.Compactness.Compact`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html) |
| Hyperreal ordered field | Present | [`Hyperreal`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Hyperreal.html) |
| Infinitesimal/infinite size and standard part | Present through generalized ordered-field APIs | `ArchimedeanClass` and `StandardPart`, imported by `Hyperreal` |
| Additive contents | Present | [`AddContent`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/AddContent.html) |
| Carathéodory extension from sigma-subadditive content | Present | [`OfAddContent`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/OfAddContent.html) |
| Conditional expectation and martingales | Substantial existing theory | `Mathlib/Probability` and `Mathlib/MeasureTheory` |

The hyperreal module itself records transfer via the first-order Łoś theorem as a TODO.
The dependent `Filter.Product` currently has the quotient, representative coercion, and
an inhabited instance, but lacks the finite-power/map ergonomics this project needs.

## What is not present as an integrated Lean library

At the pinned revision, repository source searches do not find a subject-level API for:

- generic star extensions of types, sets, and functions;
- automatic nonstandard transfer;
- a developed hypernatural API;
- internal sets and internal functions in the nonstandard-analysis sense;
- overspill/underspill;
- a reusable countable-saturation package for this setting;
- hyperfinite sums/cardinality as an NSA layer;
- Loeb measure or Loeb integration; or
- graded Loeb product/section/Fubini theorems.

This is why the project should use existing quotient, topology, and measure
infrastructure without waiting for a full NSA framework.

## Nonstandard arithmetic in Lean

There are two different starting points:

1. A hypernatural type could be defined as a germ/ultraproduct of natural-number
   sequences and inherit pointwise algebra/order.
2. Mathlib's model theory supplies compactness, elementary extensions, and Łoś-style
   tools from which nonstandard models can be constructed abstractly.

Neither starting point currently supplies a developed subject library for standard
systems, cuts, overspill, hyperfinite induction/sums, or models of Peano arithmetic.
Those topics should not be dependencies of Loeb probability.

## Other theorem provers

### Isabelle/HOL

Isabelle's official `HOL-Nonstandard_Analysis` session is the strongest mature
Robinson-style comparison point. It contains ultrapower/star constructions,
hypernaturals and hyperreals, lifted sets and functions, transfer support, and
nonstandard treatments of limits, continuity, differentiation, series, and complex
analysis.

Primary source:
[Isabelle/HOL Nonstandard Analysis session](https://isabelle.in.tum.de/library/HOL/HOL-Nonstandard_Analysis/document.pdf).

It is a useful ergonomic reference for star lifting and transfer, but it does not
replace the Loeb-measure and graded-Fubini work planned here.

### ACL2(r)

ACL2(r) has a mature syntactic/internal-external discipline with standardness,
infinitesimals, limited values, standard part, and automated support for nonstandard
calculus.

Primary source:
[ACL2(r) documentation](https://acl2.org/doc/index-seo.php?path=5216%2F7456%2F865%2F6740%2F820%2F7442&xkey=ACL2____NOTE-3-5_82R_92).

It is most relevant as a comparison for sound control of external reasoning, less as
a direct guide to Lean's quotient-and-typeclass architecture.

### Rocq/Coq

A recent Rocq development formalizes the Filter Extension Principle in axiomatic set
theory as groundwork for nonprincipal ultrafilters and future NSA. It is foundational
preparation rather than a Loeb probability library.

Primary source:
[arXiv:2407.06222](https://arxiv.org/abs/2407.06222).

## Consequences for this project

1. Reuse `Filter.Product`; do not invent a second ultraproduct quotient.
2. Add the missing dependent map/finite-power API before measure theory.
3. Use compact ultrafilter limits for bounded probabilities; keep hyperreal standard
   part as a later equivalence theorem.
4. Use targeted diagonalization, not general model-theoretic saturation.
5. Treat Loeb sections/Fubini as the foundational bottleneck.
6. Keep the ordinary graph case visible as an early application.
7. Re-audit external Lean NSA projects before adopting any as a dependency; no such
   dependency is currently part of the architecture.
