# Issue seeds

These are seed titles and acceptance summaries for work that has **not yet been
opened** as issues — a planning reservoir, not a live backlog. The live backlog is the
GitHub issue tracker; entries here are removed as they become real issues, and seeds
whose milestone has already been worked may be out of date.

IDs are local planning identifiers, replaced by GitHub issue numbers once opened.

## Epics

| ID | Suggested title | Milestone | Depends on |
| --- | --- | --- | --- |
| E0 | Epic: settle foundational API decisions | M0 | — |
| E1 | Epic: ergonomic dependent ultraproduct API | M1 | E0 |
| E2 | Epic: internal sets and countable diagonalization | M2 | E1 |
| E3 | Epic: Loeb measure on finite counting ultraproducts | M3 | E2 |
| E4 | Epic: internal-graph homomorphism-density identity | M4 | E3 |
| E5 | Epic: bounded internal integration | M5 | E3 |
| E6 | Epic: graded Loeb sections and Fubini | M6 | E1, E3, E5 |
| E7 | Epic: Elek–Szegedy realization for graphs | M7 | E4, E6 |
| E8 | Epic: Hoover graded relation-sampling representation | M8 | E6 |
| E9 | Epic: bridge to graphon and relational AHK libraries | M9 | E7, E8 |
| E10 | Epic: uniform hypergraphs and full structure theories | M10 | E7/E8 as applicable |

## M0 — research and design

### D0.1 — Decide the ultrafilter hypothesis

Compare:

- fixing `Filter.hyperfilter ℕ`;
- an arbitrary nonprincipal ultrafilter on `ℕ`;
- a project predicate for countable incompleteness; and
- a more general indexed formulation.

Acceptance:

- an elaborating candidate signature for the diagonal lemma;
- proof that the canonical hyperfilter satisfies the chosen hypothesis;
- a decision record explaining which layers are generic in the filter and which need
  the stronger hypothesis.

### D0.2 — Decide the probability-ultralimit codomain

Test compact limits in:

- a subtype of `ℝ`;
- `ℝ≥0` with a bounded subtype;
- `ℝ≥0∞` or a bounded subtype; and
- hyperreals followed by standard part, as a comparison only.

Acceptance:

- constant, congruence, order-bound, and finite-additivity experiments elaborate;
- coercions into the intended `AddContent` codomain are demonstrated;
- ADR-0002 records the choice.

### D0.3 — Decide the Loeb-measure constructor

Compare:

- `MeasureTheory.AddContent.measureCaratheodory`;
- a measurable space defined by “internal modulo null” followed by a measure; and
- proving the two presentations equivalent.

Acceptance:

- a toy finite algebra is extended with the candidate API;
- the path to `loebMeasure_internal`, completeness, and internal-mod-null is explicit;
- ADR-0003 records the choice.

### D0.4 — Audit finite-power and coordinate equivalences

Acceptance:

- inventory existing mathlib equivalences for `Fin (m+n)`, sums, products, and
  reindexing;
- choose one canonical split equivalence for graded laws;
- list missing generic lemmas as M1 work units.

## M1 — dependent ultraproduct API

| ID | Suggested title | Depends on | Acceptance summary |
| --- | --- | --- | --- |
| U1 | Add representative induction and equality API for `Filter.Product` | D0.1 | One- and two-argument eliminators; eventual-equality simp theorem |
| U2 | Add coordinatewise maps for dependent filter products | U1 | `map_mk`, identity, composition, congruence |
| U3 | Prove binary product equivalence | U1, U2 | Equivalence plus projection/naturality simp lemmas |
| U4 | Prove finite dependent-product and `Fin`-power equivalences | U3 | Evaluation commutes; `n = 0` and successor examples |
| U5 | Add coordinate reindexing and finite permutation action | U4 | Identity, composition, inverse, coordinate simp lemmas |
| U6 | Package upstream candidates from M1 | U1–U5 | Minimal imports and mathlib-appropriate namespaces |

## M2 — internal sets and diagonalization

| ID | Suggested title | Depends on | Acceptance summary |
| --- | --- | --- | --- |
| I1 | Define internal sets and their carriers | U1, U2 | Representative membership iff eventual membership |
| I2 | Prove carrier extensionality under explicit nonempty hypotheses | I1 | Exact hypotheses documented; no hidden choice assumptions |
| I3 | Give internal sets a Boolean algebra and realized set ring | I1, I2 | Carrier lemmas for all operations; `IsSetRing` |
| I4 | Define internal maps, relations, and preimages | U2, I1 | Composition and carrier-preimage theorem |
| I5 | Prove the content-free diagonal lemma | D0.1, I3 | Reusable theorem with no measure imports |
| I6 | Derive increasing-envelope and null-cover forms | I5, D0.2 | Statements match later AddContent proof needs |

## M3 — Loeb measure

| ID | Suggested title | Depends on | Acceptance summary |
| --- | --- | --- | --- |
| L1 | Implement compact ultralimits | D0.2 | Tendsto, congruence, constants, continuous maps |
| L2 | Implement ultralimits of probability values | L1 | Bounds, zero/one, finite additivity operations |
| C1 | Define normalized counting measure for varying finite types | — | Probability instance and finite-sum lemmas |
| C2 | Define internal content | I2, L2, C1 | Representative independence, empty/univ values |
| C3 | Prove finite additivity of internal content | I3, C2 | Disjoint-union theorem in the final codomain |
| C4 | Construct the internal `AddContent` | C3, D0.3 | Content on realized set ring |
| C5 | Prove sigma-subadditivity/countable additivity | I5, I6, C4 | Uses named diagonal API, not ad hoc quotient proof |
| C6 | Construct Loeb measurable space and measure | C5 | Probability measure; internal value theorem |
| C7 | Prove completeness and null-set characterization | C6 | Countable union of null sets; complete measure |
| C8 | Prove internal-mod-null and epsilon approximation theorems | C7 | Both downstream working forms |
| C9 | Prove atomlessness under growing stage cardinalities | C8 | Hypothesis separate from base construction |

## M4 — first application

| ID | Suggested title | Depends on | Acceptance summary |
| --- | --- | --- | --- |
| G1 | Define internal graphs on ultraproduct vertex spaces | I4, U4 | Symmetry and irreflexivity transported |
| G2 | Define internal homomorphism events | G1, U4, U5 | Event is internal and permutation-compatible |
| G3 | Relate finite event cardinality to homomorphism count | G2 | Normalized counting identity |
| G4 | Prove the homomorphism-density ultralimit theorem | G3, C6 | One theorem for every fixed finite simple graph |

## M5 — internal functions

| ID | Suggested title | Depends on | Acceptance summary |
| --- | --- | --- | --- |
| F1 | Define uniformly bounded internal real functions | U2, L1 | Quotient/representative API and pointwise lift |
| F2 | Prove Loeb measurability of lifted internal functions | F1, C8 | Closed-interval preimages handled |
| F3 | Prove the internal integral formula | F2, C6 | Integral equals stagewise ultralimit |
| F4 | Derive the normalized finite-average formula | F3, C1 | Explicit `Finset.sum` corollary |
| F5 | Investigate bounded internal lifting modulo a.e. equality | F3, C8 | Research issue before committing to public theorem |

## M6 — graded Loeb Fubini

| ID | Suggested title | Depends on | Acceptance summary |
| --- | --- | --- | --- |
| P1 | Define graded probability spaces and canonical split maps | D0.4 | Axioms typecheck; painless degree zero |
| P2 | Construct Loeb structures on every finite power | U4, C6 | Transported measurable space and measure |
| P3 | Prove permutation invariance | U5, P2 | Measurable and measure-preserving |
| P4 | Define internal sections and section-content functions | I4, P2 | Internal section theorem |
| P5 | Prove internal set Fubini | F3, P4 | Finite-stage Fubini transfers |
| P6 | Extend section measurability to all Loeb-measurable sets | C8, P5 | Full degree-`m+n` measurable space |
| P7 | Prove measurable section measures and set Fubini | P6 | Indicator/set form |
| P8 | Prove bounded-function Fubini | P7, F3 | Public function form |
| P9 | Bundle Loeb powers as a graded probability space | P1, P3, P7, P8 | M6 gate example compiles |

## Application branches

### Elek–Szegedy (`k = 2`)

| ID | Suggested title | Depends on |
| --- | --- | --- |
| ES1 | Define coordinate and lower-face sigma-algebras | P9 |
| ES2 | State and prove graph-level total independence | ES1 |
| ES3 | Build the separable singleton-coordinate factors | ES2 |
| ES4 | Prove/find the independent-complement theorem for the pair layer | ES3 |
| ES5 | Construct a symmetric realization into `[0,1]^3` | ES4 |
| ES6 | Integrate the top coordinate to obtain a graphon | ES5 |
| ES7 | Prove preservation of homomorphism densities | ES6, G4 |

### Hoover I

| ID | Suggested title | Depends on |
| --- | --- | --- |
| H1 | Define measurable finite-arity relations on graded spaces | P1 |
| H2 | Define finite sample laws and prove permutation invariance | H1 |
| H3 | Relate internal relation samples to finite-dimensional ultralimits | H2, P9 |
| H4 | Audit weak convergence, Hewitt–Savage, and reverse martingales | H3 |
| H5 | Formalize Hoover's graded relation-sampling theorem | H3, H4 |
| H6 | Scope the latent-uniform functional representation as a new epic | H5 |

## Good first issues

Once M1 starts, likely onboarding issues include:

- representative constructor simp lemmas for `Filter.Product`;
- degree-zero and degree-one finite-power equivalence lemmas;
- documentation examples for coordinate reindexing;
- normalized counting-measure finite-sum lemmas; and
- root-import/documentation updates after a module gate.

Do not label a quotient-lift well-definedness proof or a measurable-space instance
design task as a good first issue merely because it is short.
