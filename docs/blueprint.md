# Declaration blueprint

This is a declaration-level planning artifact for layers **not yet implemented**. It is
not a second specification: compiled Lean declarations and accepted decision records
take precedence, and where code exists it supersedes what is written here.

The rule is uniform and needs no updating: **a section here is provisional exactly when
it has no corresponding compiled module**, and where a module exists its docstrings are
the reference. Names, hypotheses, and universe parameters in an unimplemented section
may all change when the corresponding unit is written.

## Dependency DAG

```text
UProd representatives/maps
  ├── finite power equivalence ──→ coordinate maps/permutations
  └── internal-set quotient ─────→ carrier/Boolean algebra
                                      ↓
                            diagonal/saturation lemmas

compact probability ultralimit
  └── internal content ←────────── carrier/Boolean algebra
          ↓
   sigma-subadditive AddContent
          ↓
      Loeb measure
      ├── increasing envelope   (needs content, hence here and not at M2)
      ├── internal value theorem
      ├── null/completion characterization
      └── internal approximation
             ↓
      bounded internal functions
             ↓
       section-content function
             ↓
         graded Fubini
```

## Layer U — dependent ultraproducts

Core alias:

```lean
namespace Loeb

abbrev Ultraproduct
    (U : Ultrafilter ι) (X : ι → Type*) :=
  (U : Filter ι).Product X

end Loeb
```

**Layer U is implemented.** By the rule above, the modules are the reference and this
sketch is superseded: see `LoebMeasure/Ultraproduct/` for the representative,
functor, product, finite-power, and coordinate APIs, and their docstrings for the
declarations and conventions. No declaration list is kept here, because a parallel
inventory drifts — this one had already gone stale on `map_mk`, which merged as
`map_ofFun`.

What remains recorded below is the design content that is *not* derivable from the
code: why the layer is shaped this way, and the conventions later layers must respect.

`Filter.Product` provides no canonical representative selection. Everything downstream
is defined by quotient lifting through those eliminators, with representative
independence proved from eventual equality. The eliminators should follow the existing
`Filter.Germ.inductionOn` precedent exactly: theorems marked `@[elab_as_elim]`.

Do not duplicate a lemma already available for `Filter.Germ`; either generalize it to
the dependent product or reuse it through a proved equivalence.

### Canonical coordinate split (settled by D0.4)

Plain finite powers `Fin n → Ω` use **one** canonical split, adopted from mathlib:

```lean
Fin.appendEquiv m n : (Fin m → Ω) × (Fin n → Ω) ≃ (Fin (m + n) → Ω)
```

wrapped as `Loeb.splitEquiv`. Fixed conventions:

- `splitEquiv` is an opaque `def`, not an `abbrev`: a transparent alias would not
  insulate downstream code from a change of underlying equivalence. Its wrapper simp
  lemmas — forward in `Fin.castAdd`/`Fin.natAdd` form, and both `symm` components —
  are the intended interface, and graded laws use only them.
- Graded laws must not restate ad hoc equivalences; `finSumFinEquiv` remains available
  for index-level reindexing arguments but is not the tuple-level split.
- The permutation action `permute σ x = x ∘ σ` is a **contravariant pullback (right
  action)**: `permute (σ * τ) = permute τ ∘ permute σ`. This is the natural tuple
  convention and is *not* the covariant `MulAction` convention, which would precompose
  with `σ⁻¹`. Downstream statements must not silently assume covariance; `permute_mul`
  is deliberately not a simp lemma so that rewriting cannot pick an orientation.
- Measurability comes in two regimes that must stay distinguished: lemmas for the
  standard `MeasurableSpace.pi` powers use mathlib's inferred instances, whereas graded
  statements take the measurable space at each degree as data and carry compatibility
  as a hypothesis. The former discharge the latter.

Note the distinction this preserves: the `finitePiEquiv`/`finPowerEquiv` *ultraproduct*
equivalences are a different thing from the canonical split, which is about plain finite
powers `Fin n → Ω`. Compatibility between the two is still deferred, because
`splitEquiv` has not landed; when it does, it must respect the contravariance
convention above.

## Layer I — internal sets

**Layer I is implemented.** By the rule above the modules are the reference:
`LoebMeasure/Internal/Set.lean` for the type, `carrier`, the membership rule, and the
faithfulness facts; `Singleton.lean`, `BooleanAlgebra.lean`, `SetRing.lean`,
`Function.lean`, and `Relation.lean` for the rest. No declaration sketch is kept here.

What remains recorded is the design content not derivable from the code.

- **Three hypotheses, kept separate.** Nonempty fibers, the ultrafilter dichotomy, and
  countable incompleteness are three assumptions and must be introduced one at a time;
  the module docstrings record which each result consumes. Countable incompleteness
  first becomes essential in the Layer D diagonal lemma and nowhere earlier.
- `InternalSet` deliberately quantifies over *all* stagewise subsets and should stay
  that way. General measured families will add a separate `InternalMeasurableSet`
  with a forgetful map to `InternalSet`; finite counting stages identify the two
  because every stagewise set is measurable. The generalization risk therefore lives
  in the domain of `internalContent`, not in the basic internal-set layer, and the
  M2/M3 issues should record that boundary explicitly.

- **Carriers form a set algebra**, from which the ring `MeasureTheory.AddContent`
  consumes is derived. The structure each carrier law needs is not uniform: `⊥` uses
  properness, `⊤` and intersection ordinary filter laws, union and complement the
  ultrafilter dichotomy, monotonicity nothing beyond filter laws — and none of them
  nonempty fibers or countable incompleteness.
- **Quotient data and its realization stay separate**: no `CoeFun`, as with `carrier`.
- **An internal relation is an alias** for an internal set on the stagewise finite
  powers, so internality and the Loeb measure are defined on that side;
  `finPowerEquiv` appears only in the separately named `tupleCarrier` realization,
  never inside the alias.
- **Points are internal**: `InternalSet.singleton` lives in its own module rather than
  in the core seam, which keeps `Internal/Set.lean`'s representative-only import intact.

## Layer D — diagonalization

**Implemented**: `Filter.IsCountablyIncomplete` and the selection theorem in
`LoebMeasure/Internal/Diagonal.lean`, and the content-free saturation consequences in
`LoebMeasure/Internal/Saturation.lean` — including the eventual-emptiness form that is
continuity at `∅` for the internal content. Their docstrings are the reference. The hypothesis
was settled by ADR-0001 — a predicate on `Filter` rather than on `Ultrafilter`, with
properness deliberately separate — and the diagonalization consumes no ultrafilter
property.

Four mathematical forms were planned, and all four have landed — but in **two different
layers**, which is the durable point. The split was by whether a form mentions content:

| Form | Where it landed |
| --- | --- |
| decreasing nonempty intersection | M2, `Internal/Saturation.lean` |
| the form giving sigma-subadditivity | M2, `Internal/Saturation.lean` — eventual emptiness, continuity at `∅` in combinatorial dress |
| increasing envelope (Elek–Szegedy Lemma 2.4) | M3, `Measure/Envelope.lean` — it preserves *limiting content*, so it could not be stated at M2 |
| null cover for countable unions | M3, `Measure/Approximation.lean` as `loebMeasure_eq_zero_iff` |

That boundary is worth keeping in mind for later layers: a saturation statement belongs
to the diagonal layer exactly when it can be phrased without a measure.

Carrier-level equivalences belong to Layer I, not here: with nonempty fibers,
`carrier(A).Nonempty ↔ ∀ᶠ i, (A i).Nonempty` holds for any filter, while passing from
the quotient-level inequality `A ≠ InternalSet.empty` to eventual nonemptiness — and
carrier injectivity — use the ultrafilter dichotomy and no countable incompleteness
(ADR-0001).

## Layer L — compact probability ultralimits

**Layer L is implemented**, and not where this section originally planned. The generic
compact-Hausdorff wrapper turned out to be entirely about mathlib objects, so it went to
the mirror directory as
`LoebMeasure/Mathlib/Topology/Compactness/Ultralimit.lean` rather than to a
`LoebMeasure/Ultralimit/Compact.lean`, which never existed. The `ℝ≥0∞` specialization is
`LoebMeasure/Ultralimit/Probability.lean`. Both docstrings are the reference.

The durable conclusions:

- **Hypotheses are per-result, not per-module.** `ultralimit_const` needs only
  `[T2Space K]`, and `ultralimit_comp` needs compactness on the *source* alone. Stating
  the whole file under one blanket assumption would have been the easy mistake.
- **`ℝ≥0∞` throughout, with no conversion layer** (ADR-0002). It is compact Hausdorff
  with continuous addition at the pinned revision, and is already the
  `MeasureTheory.AddContent` codomain.
- **The specialization never unfolds `Ultrafilter.lim`.** Everything in the probability
  module goes through the generic API, so a change there propagates rather than breaks.
- **Scaling needs `c ≠ ∞`, not `0 < c < ∞`** — `(∞ * ·)` is discontinuous at `0`, while
  at `c = 0` the map is constant. That asymmetry is easy to get wrong and is recorded in
  `ultralimit_const_mul`.

## Layer M — content and Loeb measure

C6's Carathéodory construction went into a new `LoebMeasure/Measure/Loeb.lean` rather
than extending `LoebMeasure/Measure/Construction.lean` as this section originally
planned: that module's docstring scopes it to σ-subadditivity, and the construction also
needs the mirror directory's `OfAddContent`, which σ-subadditivity does not.

A `Measure/Completion.lean` is no longer a candidate — completeness is a two-line
wrapper around the generic mirror theorem and lives beside the construction. C7a took
`LoebMeasure/Measure/Envelope.lean`, kept separate from the approximation work because
it mentions no outer measure and no `loebMeasure`, and C7b took
`LoebMeasure/Measure/Approximation.lean`. No module candidates remain outstanding; C8
extends the approximation module, which is scoped to internal approximation rather than
to the one-sided outer bound specifically.

**Implemented**: `normalizedCounting` in `LoebMeasure/Measure/Counting.lean` (a wrapper
around mathlib's `uniformOn univ`), and `internalContent` with its elementary values and
finite additivity in `LoebMeasure/Measure/Content.lean`. Their docstrings are the
reference and tabulate the exact stage hypotheses each result takes.

Two things the sketches here got wrong, worth recording since they were design
expectations rather than typos: within the content layer nonemptiness is needed only for
the normalization results (ADR-0002's distinction) — it acquires a second, distinct role
at the carrier transport below — and the raw evaluator's bottom value and bounds need no
finiteness at all. Additivity is stated against the Boolean `⊔` rather than a set
union, with disjointness coming from the Boolean structure on `InternalSet` and no
carrier involved.

The transport to the realized carriers is **implemented**: `internalAddContent` in
`LoebMeasure/Measure/Packaging.lean`, built by `IsSetRing.addContent_of_union` from the
empty value and disjoint-union additivity, with `internalAddContent_carrier` evaluating
it. Its docstring is the reference.

Nonemptiness acquires a **second, distinct role** there, which the sketches above did
not anticipate: besides normalization, it is what makes `carrier_injective` available,
and hence what lets the content factor through `carrier` representation-independently.
It is passed as an explicit argument, not an instance, to keep that visible.

σ-subadditivity is **implemented** too, in `LoebMeasure/Measure/Construction.lean`, on
ADR-0003's accepted route: M2's saturation gives continuity at `∅` — the contents are
eventually *equal* to zero, not merely convergent — then
`addContent_iUnion_eq_sum_of_tendsto_zero` and
`isSigmaSubadditive_of_addContent_iUnion_eq_tsum`. `IsCountablyIncomplete` enters the
measure layer there, as an explicit argument.

The construction itself is **implemented**, in `LoebMeasure/Measure/Loeb.lean`: the last
step of ADR-0003's route, `AddContent.measureCaratheodory`, applied to that
σ-subadditivity and to I3's set ring weakened to a semiring. No new measure-theoretic
argument occurs there. The stable user-facing declarations:

```lean
@[reducible] noncomputable def loebMeasurableSpace
    (hX : ∀ i, Nonempty (X i)) :
    MeasurableSpace (Ultraproduct U X)

noncomputable def loebMeasure
    (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i)) :
    @Measure (Ultraproduct U X) (loebMeasurableSpace hX)

@[simp] theorem loebMeasure_internal
    (hU) (hX) (A : InternalSet U X) :
    loebMeasure hU hX A.carrier = internalContent U A

theorem measurableSet_internal
    (hX) (A : InternalSet U X) :
    MeasurableSet[loebMeasurableSpace hX] A.carrier

instance : IsProbabilityMeasure (loebMeasure hU hX)

instance : (loebMeasure hU hX).IsComplete
```

The hypotheses carry `U` and `X`, so those are implicit rather than explicit as this
sketch originally had them. Every declaration also sits under the ambient stage instances
`[∀ i, MeasurableSpace (X i)]`, `[∀ i, Finite (X i)]`, `[∀ i, MeasurableSingletonClass
(X i)]`, since the content is built from the stage measures; the separation below is
about the two *explicit* hypotheses only.

Of those two, `loebMeasurableSpace` and `measurableSet_internal` take `hX` alone, because
the Carathéodory σ-algebra of an induced outer measure exists whether or not that outer
measure is σ-subadditive; countable incompleteness enters only where the extension is
shown to be a measure. Both are `Prop`-valued, so proof irrelevance means there is no
coherence obligation and no canonical proof term to fix.

`loebMeasurableSpace` is `@[reducible]` because mathlib's linter asks it of any definition
whose result is a class, and this project promotes warnings to errors. It is *not* needed
for `loebMeasure` to elaborate at that space: a semireducible `def` unfolds during
unification just as well, as removing the attribute confirms.

Completeness is not supplied by the Carathéodory API, but it does **not** need a direct
proof here: the mirror directory supplies the generic
`MeasureTheory.AddContent.measureCaratheodory_isComplete` — no finiteness or
probability hypotheses — so the Loeb instance *wraps* that theorem rather than
reproducing its argument (ADR-0003).

The characterizations below are the genuinely substantive part: they use finite total
mass and the Layer D diagonal lemma, not just the construction. They are reached in
three units rather than one:

* **C7a — the internal envelope**, **implemented** in `LoebMeasure/Measure/Envelope.lean`:
  Elek–Szegedy Lemma 2.4, that an arbitrary sequence of internal sets has a single
  internal superset whose content *equals* the supremum of the contents of the finite
  partial unions. The equality is the point; a mere upper bound would be satisfied by
  `⊤`. This is the unit that collapses a countable internal cover to one internal set,
  and it consumes `Filter.IsCountablyIncomplete.exists_forall_eventually_mem` directly
  rather than routing through M2's saturation. Its docstring is the reference, including
  why it needs neither stage nonemptiness nor stage finiteness;
* **C7b — internal outer approximation**, **implemented** in
  `LoebMeasure/Measure/Approximation.lean`: the Loeb measure of an **arbitrary** set is
  the infimum of the contents of the internal sets containing it, with an ε-form
  producing one such superset. No measurability hypothesis, since the Loeb measure is the
  induced outer measure on every set. `loebOuterMeasure` became public here and
  `loebMeasure_eq_loebOuterMeasure` is the pointwise bridge, deliberately not `simp` so
  that `loebMeasure_internal` stays the normal form. `inducedOuterMeasure_eq_iInf` proves
  this very shape generically but is unavailable, since its hypothesis `PU` asks the
  family to be closed under countable unions and I3 gives internal carriers only a ring.
  C7a stands in for that missing closure, and this is where it is spent;
* **C8 — measurable approximation**, **implemented** in the same module: nullity by
  internal covers of small content, `exists_internal_symmDiff_lt`, an internal
  representative modulo null, and `loebMeasurable_iff_internal_mod_null`. The difficulty
  is uneven: the first two are short, while `exists_internal_symmDiff_eq_zero` is the
  real work and is where **C7a is spent a second time**, in the increasing direction.
  The reverse implication of the characterization is the only theorem in the library
  whose proof consumes completeness.

The characterizations, as implemented:

```lean
theorem loebMeasurable_iff_internal_mod_null
    (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (s : Set (Ultraproduct U X)) :
    MeasurableSet[loebMeasurableSpace hX] s ↔
      ∃ A : InternalSet U X,
        loebMeasure hU hX (s ∆ A.carrier) = 0

theorem exists_internal_symmDiff_lt
    (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hs : MeasurableSet[loebMeasurableSpace hX] s) (hε : 0 < ε) :
    ∃ A : InternalSet U X, s ⊆ A.carrier ∧
      loebMeasure hU hX (s ∆ A.carrier) < ε
```

`exists_internal_symmDiff_lt` also returns `s ⊆ A.carrier`, which its proof produces for
free and which callers wanting a one-sided approximation would otherwise re-derive.

Both carry `hU` even though the σ-algebra does not: the approximation is a statement
about the *measure*, and the increasing-envelope diagonal argument is where saturation
is consumed.

Measurability is what makes the two-sided estimate available at all:
`exists_internal_subset_lt_content_add` complements C7b's outer approximation of `sᶜ`,
using the Boolean algebra on internal sets and total mass `1`.

### Points, and atomlessness

**C9, implemented**, in two modules whose separation is mathematical rather than
organizational.

`LoebMeasure/Measure/Points.lean` has the **measure of a point**. A singleton of the
ultraproduct is *already* the carrier of an internal set — eventual stagewise equality is
equality in the ultraproduct — so the computation factors one step per layer,
`InternalSet.singleton → internalContent_singleton → loebMeasure_singleton`, using none of
C7 or C8:

```lean
theorem loebMeasure_singleton
    (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (x : Ultraproduct U X) :
    loebMeasure hU hX {x} = U.ultralimit fun i ↦ ((Nat.card (X i) : ℝ≥0∞))⁻¹
```

`LoebMeasure/Measure/Atomless.lean` has **exact bisection** and the **atomlessness** M3
promised. The bisection is stated first because the proof establishes it before positivity
is used anywhere:

```lean
theorem exists_measurableSet_subset_measure_eq_half (hU) (hX) (hcard)
    (hs : MeasurableSet[loebMeasurableSpace hX] s) :
    ∃ t ⊆ s, MeasurableSet[loebMeasurableSpace hX] t ∧
      loebMeasure hU hX t = loebMeasure hU hX s / 2
```

and atomlessness is then a corollary, half of a positive finite measure being positive and
strictly smaller:

```lean
theorem exists_measurableSet_subset_measure_lt (hU) (hX)
    (hcard : Tendsto (fun i ↦ Nat.card (X i)) (U : Filter ι) atTop)
    (hs : MeasurableSet[loebMeasurableSpace hX] s) (hpos : 0 < loebMeasure hU hX s) :
    ∃ t ⊆ s, MeasurableSet[loebMeasurableSpace hX] t ∧
      0 < loebMeasure hU hX t ∧ loebMeasure hU hX t < loebMeasure hU hX s
```

**The two are different properties**, and the module boundary exists to keep them apart.
Mathlib's note on `NullSingletonClass` records that its planned `NoAtoms` — the shape
above — implies null singletons and that the converse fails; the countable–cocountable
probability measure has every singleton null while the whole space is an atom. So the
point-mass package does not close the milestone on its own, and the weaker property does
not get to occupy the name "atomless".

**Splitting is what costs.** `exists_internal_le_content_eq_half` gives every internal set
an internal half, stagewise via `Set.exists_subset_card_eq`. Where the represented set has
even cardinality the stagewise halving is exact; where it is odd, one point is discarded.
The growth hypothesis is what makes that vanish: `2⌊n/2⌋ ≤ n ≤ 2⌊n/2⌋ + 1` differ by at
most one point of the stage, worth `(Nat.card (X i))⁻¹`, which tends to `0` by
`ultralimit_inv_natCast_eq_zero`. So the halving is exact in the limit whatever the
stagewise parities do. The estimates run on `2 * internalContent` rather than
`internalContent / 2`, so division appears only in the statement and the final
rearrangement, never inside the inequalities, and truncated subtraction never appears.
Bisection then combines this with C8.

Divergence of the stage cardinalities is written as mathlib's `Tendsto _ atTop` rather
than a bespoke predicate — the two say the same thing, and a new name would only add
conversion lemmas. It is genuinely needed: on subsingleton stages the ultraproduct is a
single atom, recorded as the compiled
`loebMeasure_singleton_eq_one_of_subsingleton`. Only the sufficient direction is proved;
that theorem is a counterexample to dropping the hypothesis, not a converse.

`nullSingletonClass_loebMeasure` is a **theorem, not an instance**: the divergence
hypothesis does not appear in `loebMeasure hU hX`, so typeclass inference cannot recover
it, unlike `hU` and `hX` which do appear. Callers use `haveI`. The bisection and
atomlessness results are simply invoked directly — there is no class to populate, since
mathlib's `NoAtoms` in the splitting sense is still only a TODO.

The full **Lyapunov** statement — that the range of the measure is all of `[0, 1]`, not
merely that it contains a strictly intermediate value — needs iterating the split and a
limit argument, and is not part of M3.

## Layer B — bounded internal functions

Module candidates:

```text
LoebMeasure/Integral/Bounded.lean
LoebMeasure/Integral/InternalFunction.lean
```

Not `LoebMeasure/Internal/Function.lean`, which this list once named: that module exists
and holds *internal maps* between ultraproducts — a different notion from a bounded
real-valued internal function, and one this layer will consume rather than extend.

Initial functions are uniformly bounded and real-valued:

```lean
structure BoundedInternalFunction
    (U : Ultrafilter ι) (X : ι → Type*) where
  bound : ℝ
  fn : ∀ i, X i → ℝ
  norm_le : ∀ i x, ‖fn i x‖ ≤ bound
```

The representation will likely also quotient eventually equal families. Required
public results:

```lean
def BoundedInternalFunction.lift :
    Ultraproduct U X → ℝ

theorem BoundedInternalFunction.measurable_lift
    (hX : ∀ i, Nonempty (X i)) :
    Measurable[loebMeasurableSpace hX] f.lift

theorem integral_internalFunction
    (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i)) :
    ∫ x, f.lift x ∂loebMeasure hU hX =
      probabilityUltralimit U
        (fun i => ∫ x, f.fn i x ∂normalizedCounting i)
```

The average-over-finite-types form should be an explicit corollary.

## Layer G — graded powers and Fubini

Module candidates:

```text
LoebMeasure/Graded/Basic.lean
LoebMeasure/Graded/Power.lean
LoebMeasure/Graded/Section.lean
LoebMeasure/Graded/Fubini.lean
```

Candidate bundle:

```lean
namespace Loeb.Graded

structure ProbabilitySpace (Ω : Type*) where
  mspace : (n : ℕ) → MeasurableSpace (Fin n → Ω)
  measure : (n : ℕ) → Measure (Fin n → Ω)
  probability : ∀ n, IsProbabilityMeasure (measure n)
  -- permutation measurability and preservation
  -- compatibility for splitting coordinates
  -- measurable sections and section measures
  -- Fubini

end Loeb.Graded
```

The laws need a single accepted family of equivalences between
`Fin (m + n) → Ω` and `(Fin m → Ω) × (Fin n → Ω)`. They should not be restated with
ad hoc equivalences in each theorem.

`MeasureTheory.Filtration` is the ergonomic precedent — families of measurable spaces
as explicit data with `≤` fields and `MeasurableSet[m]` statements — but it is not
directly reusable: a filtration carries several sigma-algebras on one carrier, while
the graded family lives on carriers `Fin n → Ω` varying with `n`. Do not encode the
full injection category of finite sets initially; expose canonical reindexing,
permutation, and splitting maps with their compatibility lemmas.

Required section API (`section` is a Lean keyword, so the API needs non-keyword names
such as `sectionAt`/`sectionMeasure`):

```lean
def sectionAt
    (s : Set (Fin (m + n) → Ω))
    (x : Fin m → Ω) :
    Set (Fin n → Ω)

theorem measurableSet_sectionAt ...
theorem measurable_sectionMeasure ...
theorem lintegral_sectionMeasure ...
theorem integral_sectionAt ...
```

The degree-`m+n` measurable-space hypothesis is the graded space's own `mspace
(m+n)`, not a product-space equality.

## First application seam

`LoebMeasure/GraphLimit/HomDensity.lean`. **Layer M's completion unblocks this**, and it
deliberately does *not* wait on Layer B: the ROADMAP places M4 "before building the harder
integration and Fubini layers", its gate requires the proof to use only the public M1–M3
API, and ARCHITECTURE's dependency graph branches `Measure → GraphLimit/HomDensity`
*before* `Measure → Integral`.

The route is through the Loeb measure of the internal homomorphism event and its finite
counting identity — a measure of a set, not an integral of a function — which is exactly
why no bounded integration is needed:

```lean
theorem homDensity_internalGraph
    (F : SimpleGraph (Fin k))
    (G : ∀ i, SimpleGraph (X i)) :
    loebHomDensity U F (internalGraph U G) =
      probabilityUltralimit U
        (fun i => finiteHomDensity F (G i))
```

E4 froze the commitments this sketch left open: `F` is a *fixed* `SimpleGraph (Fin k)`;
`G` varies over finite nonempty stages; density counts **all** edge-preserving vertex
maps — neither induced nor injective — normalized by `|X i| ^ k`; and the homomorphism
event lives on `InternalSet U (fun i ↦ Fin k → X i)`, the stagewise-power side.

**G1 is implemented** in `LoebMeasure/GraphLimit/InternalGraph.lean`, and supersedes this
sketch's `internalGraph`. It gives two deliberately distinct objects rather than one:
`internalEdgeRelation U G : InternalRelation U X 2` on the stagewise-pair side, and
`ultraproductGraph U G : SimpleGraph (Ultraproduct U X)` on the realized side, related by
the computation rule `Adj (ofFun x) (ofFun y) ↔ ∀ᶠ i in U, (G i).Adj (x i) (y i)`. The
naming keeps the realized graph from being confused with its internal relation.

Two durable points from it. Symmetry and irreflexivity are **transported** from the stage
graphs rather than imposed by `SimpleGraph.fromRel`. That is not a correctness question —
the wrapper would give the identical graph here, the relation being already symmetric and
irreflexive — but a question of where the obligation lives: building the fields directly
makes the elaborator demand the transport proofs instead of manufacturing the structure.
And `finPowerEquiv` appears only in a private bridge lemma; no definition in that module
mentions it.

G1 takes **no additional hypotheses** — no finiteness, nonemptiness, measurability, or
countable incompleteness, and no measure-layer import. What the ultrafilter supplies and
G1 genuinely uses is **properness**, for looplessness; the dichotomy is not used.

**G2 is implemented** too, in `LoebMeasure/GraphLimit/HomEvent.lean`. `internalHomEvent`
is built **only** as a finite intersection of coordinate pullbacks of
`internalEdgeRelation` — the construction `InternalRelation.comap` exists for — with the
direct stagewise description appearing as `internalHomEvent_eq_ofFun`, an **equality of
internal sets** rather than a competing definition. That it is an equality and not a
carrier characterization is the load-bearing part: without nonempty fibers `carrier` is
not known to be injective, so agreeing carriers would not give agreeing internal sets.

The intersection is indexed by **ordered** adjacent pairs in `Fin k × Fin k` rather than
by `F.edgeFinset : Finset (Sym2 _)`: `Sym2` would force a non-canonical choice of
orientation to build the coordinate map, while duplicating each undirected edge is harmless
since `F` and every `G i` are symmetric.

Finiteness of the pattern is discharged in **one place**, where `adjPairs` enumerates
`Fin k × Fin k` with `Finset.univ`; the two `Finset` inductions are generic over an
already-given `Finset`. From there *no filter-level finite-intersection argument is needed
anywhere*: the equality collapses the intersection at the level of representative
functions — literally equal as functions, so the quotient step is `congrArg` — leaving
representative membership as just `mem_carrier_ofFun`, and the realized rule needs no such
argument either since `tupleCarrier` is a preimage.
`InternalRelation.tupleCarrier_top` and `tupleCarrier_inf` were added for exactly that —
the realized semantics of conjunction, and nothing more speculative.

**G3 is implemented** in `LoebMeasure/GraphLimit/HomDensity.lean`, closing the E4 gate:

```lean
theorem loebMeasure_internalHomEvent (hU) (hXk : ∀ i, Nonempty (Fin k → X i)) (F) (G) :
    loebMeasure (X := fun i ↦ Fin k → X i) hU hXk
        (InternalSet.carrier (internalHomEvent U F G))
      = U.ultralimit fun i ↦ finiteHomDensity F (G i)
```

Three durable points. First, `finiteHomDensity` is defined **independently of measure
theory**, as `(homomorphismSet F G).ncard / (Nat.card X) ^ k` in `ℝ≥0∞`. Defining it as
the `normalizedCounting` value would have made the stage identity true by definition and
verified nothing — in particular it would not have checked that the normalization is the
intended `|X| ^ k`. That check is the content of
`normalizedCounting_homomorphismSet`, which holds because `Nat.card_fun` and `Nat.card_fin`
identify `Nat.card (Fin k → X)` with `Nat.card X ^ k`.

Second, the hypotheses stratify cleanly across the three statements: the density needs a
**finite target only**; the stage identity adds the **discrete measurable structure** and
still no nonemptiness; the Loeb theorem adds `hU` and nonemptiness. And the nonemptiness it
adds is of the *powers*, which is weaker than stage nonemptiness and free when `k = 0`.

Third, the Loeb step itself is four rewrites — `internalHomEvent_eq_ofFun`,
`loebMeasure_internal`, `internalContent_ofFun`, then the stage identity under the
ultralimit. That cheapness is the point of M4 preceding the integration layers, and the
measure is taken on the ultraproduct of stagewise powers throughout, so no ordinary product
measurability is assumed anywhere.

## Stability policy

- Names in a section with no corresponding compiled module are provisional; names in an
  implemented layer are not.
- Once a milestone gate is reached, renaming its public declarations requires a
  migration note and issue.
- Mathematical assumptions may never be hidden merely to preserve a provisional
  signature.
