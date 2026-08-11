# Roadmap

This roadmap is dependency-driven rather than calendar-driven. Each milestone ends in
a compiled mathematical capability that can support the next one. Milestones are also
the recommended GitHub milestones; their issue-level decomposition is in
[docs/issue-seeds.md](docs/issue-seeds.md).

## Project target

The common foundation should support:

1. ultraproduct probability spaces and their internal sets and bounded functions;
2. a countably additive Loeb measure with an internal approximation API;
3. separate Loeb measurable spaces and measures on every finite power;
4. measurable sections and Fubini for those larger, graded measurable spaces;
5. Hoover's ultraproduct relation-sampling representation; and
6. the Elek–Szegedy finite-to-ultraproduct-to-graphon route, first for graphs.

The project does not initially depend on a universal star transform, automatic
first-order transfer, hypernaturals, overspill, or infinitesimal calculus.

## Success levels

The target papers contain several distinct projects. Tracking them separately avoids
calling the entire program “almost done” after only the Loeb construction.

| Track | First complete target | Later target | Stretch target |
| --- | --- | --- | --- |
| Core | Loeb measure on finite counting ultraproducts | bounded integration and graded Fubini | general measured families |
| Elek–Szegedy | fixed-graph hom-density identity | graph (`k = 2`) realization | uniform hypergraphs and the full paper |
| Hoover | graded relation-sampling representation | latent-uniform functional representation | equivalence and uniqueness |

## M0 — Scope and API decisions

Goal: turn the research proposal into decisions that can be tested against pinned
mathlib.

- Audit `Filter.Product`, compact ultrafilter limits, `AddContent`, completion, and
  finite-power APIs.
- Decide how the countable-incompleteness/freeness hypothesis is represented.
- Decide the codomain used to construct ultralimits of probability values.
- Compare a direct null-completion construction with `AddContent.measureCaratheodory`.
- Record each decision in `docs/decisions/`.

Gate:

- the first three decision records are accepted;
- candidate declarations for M1–M3 elaborate in scratch files; and
- no downstream issue assumes a stronger saturation theorem than the chosen
  ultrafilter hypothesis provides.

## M1 — Ergonomic dependent ultraproducts

Goal: place a probability-oriented API over mathlib's low-level
`Filter.Product`.

- Representative induction and equality lemmas.
- Maps induced by coordinatewise maps.
- Binary products, finite dependent products, and finite powers.
- Coordinate projections and equivalences involving `Fin n → X`.
- Finite permutation actions and their compatibility laws.

Gate:

- the equivalence
  `Product U (fun i => Fin n → X i) ≃ (Fin n → Product U X)` is usable without
  unfolding quotients;
- coordinate maps and permutations have simp lemmas; and
- generic results suitable for mathlib live under `Filter.Product`.

## M2 — Internal sets and diagonalization

Goal: expose internal subsets of an ultraproduct as a Boolean algebra of actual sets.

- Quotient representation of internal set families.
- A separate realization/carrier map into `Set (Loeb.Ultraproduct U X)`.
- Membership, equality, complement, union, intersection, and symmetric-difference
  lemmas.
- Internal maps, preimages, and relations.
- The countable diagonal lemma, and its content-free saturation consequences —
  in particular the eventual-emptiness form that is continuity at `∅` in combinatorial
  dress.

The increasing-envelope theorem is **not** here. Elek–Szegedy's Lemma 2.4 preserves the
limiting internal content, so it cannot land before `internalContent` exists; it belongs
to M3. The countable null-cover theorem belongs later still, with the
null-set/approximation layer.

Gate:

- representative-level membership reduces to eventual membership;
- realized internal sets form a set ring;
- the diagonal theorem has a statement reusable by both measure and integration, and
  its eventual-emptiness consequence is stated in the form M3's sigma-subadditivity
  argument consumes; and
- no first-order syntax or general model-theoretic saturation is required.

## M3 — Ultralimits, internal content, and Loeb measure

Goal: construct the first genuine Loeb probability space, initially for normalized
counting measures on nonempty finite types.

- Compact ultralimit API for values in a bounded probability range.
- Internal content and independence from representatives.
- Finite additivity and normalization.
- Sigma-subadditivity/countable additivity on the internal set ring.
- Carathéodory extension (or the equivalent accepted construction).
- Null sets, completeness, internal approximation, and “internal modulo null.”
- Atomlessness as a separate theorem under growing-cardinality hypotheses.

Gate:

- every internal set is measurable and its Loeb measure is its stagewise ultralimit;
- the resulting measure is a probability measure;
- null and internal-approximation characterizations are available as downstream
  lemmas; and
- the construction is free of project-specific graph or exchangeability assumptions.

## M4 — First vertical slice: homomorphism densities

Goal: prove a useful finite-to-Loeb theorem before building the harder integration and
Fubini layers.

- Internal graphs and their edge relations.
- Pullback of an internal relation along finite coordinate maps.
- Internal homomorphism events.
- Normalized finite homomorphism density.
- Equality of Loeb measure with the ultralimit of finite homomorphism densities.

Gate:

- one theorem for every fixed finite simple graph compiles without `sorry`;
- its proof uses only the public M1–M3 API; and
- the result does not assume ordinary product measurability.

## M5 — Bounded internal functions and integration

Goal: support the function calculations used in Elek–Szegedy and later Fubini proofs.

- Pointwise ultralimit of uniformly bounded internal real functions.
- Measurability.
- Integral equals the ultralimit of finite-stage integrals/averages.
- Approximation by internal simple functions.
- A bounded internal lifting theorem, if it follows cleanly from the accepted
  measurable-space construction.

Gate:

- characteristic functions recover the M3 set API;
- the normalized finite-sum formula is a corollary; and
- the public API does not expose hyperreal standard parts.

## M6 — Graded powers, sections, and Fubini

Goal: deliver the common foundation required by both target programs.

- A `Loeb.Graded.ProbabilitySpace` structure using `Fin n → Ω`.
- Loeb structures on ultraproducts of all finite powers.
- Permutation invariance and splitting-coordinate compatibility.
- Internal sections and their section-content functions.
- Measurability of arbitrary measurable sections and section measures.
- Set and bounded-function Fubini theorems.
- The Loeb finite powers bundled as a graded probability space.

Gate:

- the theorem is stated for the full Loeb measurable space on the combined power;
- it does not assert equality with the ordinary product sigma-algebra;
- set and function forms of Fubini are both usable; and
- a small example demonstrates a section through a nontrivial coordinate split.

This is the main common-core release.

## M7 — Elek–Szegedy for graphs

Goal: obtain the `k = 2` correspondence with an ordinary graphon.

- Coordinate maps and coordinate sigma-algebras.
- Lower-face sigma-algebras.
- The graph-level total-independence statement.
- Countably generated factors needed by one internal edge event.
- An independent complement for the pair layer.
- A symmetric realization into `[0,1]^3`.
- Integration over the top coordinate to obtain a graphon.
- Agreement with the M4 homomorphism-density theorem.

Gate:

- an internal symmetric graph relation has a graphon realization preserving every
  fixed finite homomorphism density.

General `k` is not part of this gate.

## M8 — Hoover I: graded relation sampling

Goal: formalize the nonstandard sampling representation, not yet the full
Aldous–Hoover functional form.

- Measurable relations on a graded probability space.
- Laws of finite samples and their consistency.
- Exchangeability under the relevant finite permutation actions.
- Internal relations recover ultralimits of finite-dimensional laws.
- The weak-convergence, zero-one, and reverse-martingale inputs required by Hoover's
  sampling theorem.

Gate:

- the selected exchangeability class has a relation-sampling representation on a
  graded probability space.

## M9 — Standardization and existing graphon/AHK bridges

Goal: reuse standard probability and graphon theory instead of duplicating it inside
the nonstandard core.

- Interface the sampled exchangeable law with the existing graphon/relational AHK
  development.
- Compare the direct Elek–Szegedy realization with the existing graphon
  representation modulo the relevant equivalence.
- Inventory and upstream generic conditional-expectation, separable-factor, and
  measure-isomorphism lemmas as appropriate.

Gate:

- the finite-graph ultraproduct route and the existing standard representation route
  compose end to end.

## M10 — Major extensions

These are separate epics, not requirements for a first stable library:

- uniform `k`-hypergraph coordinate systems and total independence;
- equivariant separable realization and hypergraphons;
- hypergraph removal, regularity, counting, uniqueness, and testability;
- Hoover's latent-uniform functional representation;
- Hoover's full measure-algebraic equivalence and uniqueness theory;
- general Loeb spaces beyond finite counting families; and
- optional bridges to first-order Łoś or a future star/transfer library.

## Release discipline

A milestone is complete only when:

- its Lean modules build with `warningAsError`;
- there are no `sorry` declarations in its scope;
- public declarations have docstrings and stable module placement;
- the root import exposes the completed public layer;
- examples exercise the intended API without quotient unfolding; and
- the roadmap and issue dependency graph reflect any changed assumptions.
