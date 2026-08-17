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

**Implemented**: `InternalSet`, `carrier`, the membership rule, and the nonemptiness
and injectivity facts that make `carrier` faithful all live in
`LoebMeasure/Internal/Set.lean`, whose docstrings are the reference. By the rule above,
no sketch of them is kept here. The remaining Layer I units — the Boolean algebra and
set ring, internal maps and relations — are still unimplemented and sketched below.

Module candidates for the unimplemented units:

```text
LoebMeasure/Internal/Relation.lean
LoebMeasure/Internal/Diagonal.lean
```

Two recorded caveats:

- Carrier nonemptiness and injectivity are **implemented**; see
  `LoebMeasure/Internal/Set.lean`, whose docstrings record which hypothesis each one
  consumes. The durable rule they establish: nonempty fibers, the ultrafilter
  dichotomy, and countable incompleteness are three separate assumptions and must be
  introduced separately — freeness or countable incompleteness first becomes essential
  in the Layer D diagonal lemma, and nowhere earlier.
- `InternalSet` deliberately quantifies over *all* stagewise subsets and should stay
  that way. General measured families will add a separate `InternalMeasurableSet`
  with a forgetful map to `InternalSet`; finite counting stages identify the two
  because every stagewise set is measurable. The generalization risk therefore lives
  in the domain of `internalContent`, not in the basic internal-set layer, and the
  M2/M3 issues should record that boundary explicitly.

The Boolean operations, their carrier laws, and the realized carrier algebra are
**implemented**: see `LoebMeasure/Internal/BooleanAlgebra.lean` and
`LoebMeasure/Internal/SetRing.lean`. The durable design points they establish: the
carriers form a set *algebra*, from which the ring `MeasureTheory.AddContent` consumes
is derived; and the structure each law needs is not uniform — `⊥` uses properness, `⊤`
and intersection ordinary filter laws, union and complement the ultrafilter dichotomy,
and none of them nonempty fibers or countable incompleteness.

Internal maps, preimages, and relations are **implemented**: see
`LoebMeasure/Internal/Function.lean` and `LoebMeasure/Internal/Relation.lean`. The
durable design points they fix: quotient data and its realization stay separate (no
`CoeFun`, as with `carrier`); an internal relation is an *alias* for an internal set on
the stagewise finite powers, so internality and later Loeb measure are defined on that
side; and `finPowerEquiv` appears only in the separately named `tupleCarrier`
realization, never inside the alias.

## Layer D — diagonalization

**Implemented**: `Filter.CountablyIncomplete` and the selection theorem in
`LoebMeasure/Internal/Diagonal.lean`, and the content-free saturation consequences in
`LoebMeasure/Internal/Saturation.lean` — including the eventual-emptiness form that is
continuity at `∅` for the internal content. Their docstrings are the reference. The hypothesis
was settled by ADR-0001 — a predicate on `Filter` rather than on `Ultrafilter`, with
properness deliberately separate — and the diagonalization consumes no ultrafilter
property.

Required mathematical forms:

1. an increasing-envelope lemma for a sequence of internal sets, matching
   Elek–Szegedy Lemma 2.4;
2. a decreasing nonempty-intersection lemma when convenient;
3. a null-cover lemma for countable unions; and
4. a version usable to prove sigma-subadditivity of internal content.

**Only the content-free forms belong to M2**, and both are now implemented in
`LoebMeasure/Internal/Saturation.lean`: form 2 as the two nonempty-intersection
theorems, and form 4 as the eventual-emptiness theorem — continuity at `∅` in
combinatorial dress, and what makes `addContent_iUnion_eq_sum_of_tendsto_zero`
applicable at M3. Their docstrings are the reference.

Forms 1 and 3 mention content and remain deferred: the increasing envelope —
Elek–Szegedy Lemma 2.4, which preserves the *limiting internal content* — moves to M3
once `internalContent` exists, provisionally owned by C7/C8, and the null-cover lemma
later still, with the null-set/approximation layer.

Carrier-level equivalences belong to Layer I, not here: with nonempty fibers,
`carrier(A).Nonempty ↔ ∀ᶠ i, (A i).Nonempty` holds for any filter, while passing from
the quotient-level inequality `A ≠ InternalSet.empty` to eventual nonemptiness — and
carrier injectivity — use the ultrafilter dichotomy and no countable incompleteness
(ADR-0001).

## Layer L — compact probability ultralimits

Module candidates:

```text
LoebMeasure/Ultralimit/Compact.lean
LoebMeasure/Ultralimit/Probability.lean
```

The foundational wrapper should expose:

```lean
def ultralimit (U : Ultrafilter ι) (f : ι → K) : K

theorem tendsto_ultralimit :
    Tendsto f U (𝓝 (ultralimit U f))

theorem ultralimit_congr
    (h : f =ᶠ[U] g) :
    ultralimit U f = ultralimit U g

theorem ultralimit_const ...
theorem ultralimit_comp
    (hg : Continuous g) :
    ultralimit U (g ∘ f) = g (ultralimit U f)
```

Here `K` is nonempty compact Hausdorff. The probability-specific wrapper should add
order bounds and the finite-additivity operations needed by content, without exposing
irrelevant topological choice details.

## Layer M — content and Loeb measure

C6's Carathéodory construction went into a new `LoebMeasure/Measure/Loeb.lean` rather
than extending `LoebMeasure/Measure/Construction.lean` as this section originally
planned: that module's docstring scopes it to σ-subadditivity, and the construction also
needs the mirror directory's `OfAddContent`, which σ-subadditivity does not.

A `Measure/Completion.lean` is no longer a candidate — completeness is a two-line
wrapper around the generic mirror theorem and lives beside the construction. Remaining
module candidate:

```text
LoebMeasure/Measure/Approximation.lean
```

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
`isSigmaSubadditive_of_addContent_iUnion_eq_tsum`. `CountablyIncomplete` enters the
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
    (hU : (U : Filter ι).CountablyIncomplete) (hX : ∀ i, Nonempty (X i)) :
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
sketch originally had them. More importantly the two hypotheses **separate**:
`loebMeasurableSpace` and `measurableSet_internal` take only `hX`, because the
Carathéodory σ-algebra of an induced outer measure exists whether or not that outer
measure is σ-subadditive; countable incompleteness enters only where the extension is
shown to be a measure. Both hypotheses are `Prop`-valued, so proof irrelevance means
there is no coherence obligation and no canonical proof term to fix.

`loebMeasurableSpace` must be `@[reducible]` — Lean requires it of any definition whose
result is a class — which is also what lets `loebMeasure` be stated at it while being
*defined* by `AddContent.measureCaratheodory`, whose target is the Carathéodory space
written out.

Completeness is not supplied by the Carathéodory API, but it does **not** need a direct
proof here: the mirror directory supplies the generic
`MeasureTheory.AddContent.measureCaratheodory_isComplete` — no finiteness or
probability hypotheses — so the Loeb instance *wraps* that theorem rather than
reproducing its argument (ADR-0003).

The characterizations below are the genuinely substantive part: they use finite total
mass and the Layer D diagonal lemma, not just the construction.

Downstream working characterizations:

```lean
theorem loebMeasurable_iff_internal_mod_null
    (s : Set (Ultraproduct U X)) :
    MeasurableSet[loebMeasurableSpace U X] s ↔
      ∃ A : InternalSet U X,
        loebMeasure U X (s ∆ A.carrier) = 0

theorem exists_internal_symmDiff_lt
    (hs : MeasurableSet[loebMeasurableSpace U X] s)
    (hε : 0 < ε) :
    ∃ A : InternalSet U X,
      loebMeasure U X (s ∆ A.carrier) < ε
```

The exact symmetric-difference notation must follow pinned mathlib.

## Layer B — bounded internal functions

Module candidates:

```text
LoebMeasure/Internal/Function.lean
LoebMeasure/Integral/Bounded.lean
LoebMeasure/Integral/InternalFunction.lean
```

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

theorem BoundedInternalFunction.measurable_lift :
    Measurable[loebMeasurableSpace U X] f.lift

theorem integral_internalFunction :
    ∫ x, f.lift x ∂loebMeasure U X =
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

`LoebMeasure/GraphLimit/HomDensity.lean` should be implementable once Layer M exists:

```lean
theorem homDensity_internalGraph
    (F : SimpleGraph (Fin k))
    (G : ∀ i, SimpleGraph (X i)) :
    loebHomDensity U F (internalGraph U G) =
      probabilityUltralimit U
        (fun i => finiteHomDensity F (G i))
```

The exact representation of `G` may use a sigma type or dependent family. The issue
closes only when the theorem works for varying finite vertex types and the proof uses
the public internal finite-power API.

## Stability policy

- Names in a section with no corresponding compiled module are provisional; names in an
  implemented layer are not.
- Once a milestone gate is reached, renaming its public declarations requires a
  migration note and issue.
- Mathematical assumptions may never be hidden merely to preserve a provisional
  signature.
