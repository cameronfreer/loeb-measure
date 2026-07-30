# Declaration blueprint

This is a declaration-level planning artifact for the common foundation. It is not a
second specification: compiled Lean declarations and accepted decision records take
precedence. Names and universe parameters below are provisional until their M0/M1
spikes elaborate against the pinned mathlib revision.

## Dependency DAG

```text
UProd representatives/maps
  ├── finite power equivalence ──→ coordinate maps/permutations
  └── internal-set quotient ─────→ carrier/Boolean algebra
                                      ↓
                            diagonal/envelope lemmas

compact probability ultralimit
  └── internal content ←────────── carrier/Boolean algebra
          ↓
   sigma-subadditive AddContent
          ↓
      Loeb measure
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

Module candidates:

```text
LoebMeasure/Ultraproduct/Basic.lean
LoebMeasure/Ultraproduct/Map.lean
LoebMeasure/Ultraproduct/FinitePower.lean
LoebMeasure/Ultraproduct/Permutation.lean
```

Core alias:

```lean
namespace Loeb

abbrev Ultraproduct
    (U : Ultrafilter ι) (X : ι → Type*) :=
  (U : Filter ι).Product X

end Loeb
```

Generic API candidates under `Filter.Product`:

```lean
namespace Filter.Product

theorem inductionOn ...
theorem inductionOn₂ ...

def map
    (f : ∀ i, X i → Y i) :
    l.Product X → l.Product Y

@[simp] theorem map_mk ...
@[simp] theorem map_id ...
theorem map_comp ...

def prodEquiv :
    l.Product (fun i => X i × Y i) ≃
      l.Product X × l.Product Y

def finitePiEquiv (κ : Type*) [Finite κ] :
    l.Product (fun i => κ → X i) ≃
      (κ → l.Product X)

def finPowerEquiv (n : ℕ) :
    l.Product (fun i => Fin n → X i) ≃
      (Fin n → l.Product X)

end Filter.Product
```

Required laws:

- representative equality is eventual equality;
- every quotient element has a representative elimination principle;
- maps preserve identity and composition;
- product/power equivalences commute with coordinate evaluation;
- reindexing a finite power is functorial;
- a permutation and its inverse induce inverse maps.

Do not duplicate a lemma already available for `Filter.Germ`; either generalize it to
the dependent product or reuse it through a proved equivalence.

## Layer I — internal sets

Module candidates:

```text
LoebMeasure/Internal/Set.lean
LoebMeasure/Internal/Relation.lean
LoebMeasure/Internal/Diagonal.lean
```

Candidate data:

```lean
namespace Loeb

abbrev InternalSet
    (U : Ultrafilter ι) (X : ι → Type*) :=
  (U : Filter ι).Product (fun i => Set (X i))

def InternalSet.carrier
    (A : InternalSet U X) :
    Set (Ultraproduct U X)

@[simp] theorem InternalSet.mem_carrier_mk_iff
    (x : ∀ i, X i) (A : ∀ i, Set (X i)) :
    (x : Ultraproduct U X) ∈
        InternalSet.carrier (A : InternalSet U X) ↔
      ∀ᶠ i in U, x i ∈ A i

end Loeb
```

The exact coercion policy is an M2 API choice. Even if a coercion to `Set` is supplied,
the named `carrier` must remain available for readable statements.

Boolean API:

```lean
InternalSet.empty
InternalSet.univ
InternalSet.compl
InternalSet.union
InternalSet.inter
InternalSet.diff
InternalSet.symmDiff
```

with carrier lemmas for every operation. The realized carriers should be packaged as a
set ring suitable for `MeasureTheory.AddContent`.

Internal maps and relations:

```lean
def InternalMap ...
def InternalMap.toFun ...
def InternalSet.preimage ...
abbrev InternalRelation ...  -- an internal set on a finite power
```

The first relation API only needs finite arity and coordinatewise maps.

## Layer D — diagonalization

The exact freeness property is unresolved. The public theorem should isolate it rather
than fix `Filter.hyperfilter ℕ` throughout the entire library.

Required mathematical forms:

1. an increasing-envelope lemma for a sequence of internal sets, matching
   Elek--Szegedy Lemma 2.4;
2. a decreasing nonempty-intersection lemma when convenient;
3. a null-cover lemma for countable unions; and
4. a version usable to prove sigma-subadditivity of internal content.

Candidate statement shape:

```lean
theorem exists_internal_iUnion_envelope
    (A : ℕ → InternalSet U X)
    (hmono : Monotone A)
    (hμ : Tendsto (fun n => content (A n)) atTop (𝓝 t)) :
    ∃ B : InternalSet U X,
      (∀ n, A n ≤ B) ∧ content B = t
```

This statement depends on content and may live later than the underlying combinatorial
diagonal lemma. The M2 issue must first expose a content-free lemma from which this
follows.

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

Module candidates:

```text
LoebMeasure/Measure/Content.lean
LoebMeasure/Measure/Construction.lean
LoebMeasure/Measure/Completion.lean
LoebMeasure/Measure/Approximation.lean
```

Initial stage data:

```lean
variable (X : ι → Type*) [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]

def normalizedCounting (i : ι) : Measure (X i)
def internalContent (U : Ultrafilter ι) :
    InternalSet U X → ℝ≥0∞
```

Required theorems:

```lean
@[simp] theorem internalContent_empty ...
@[simp] theorem internalContent_univ ...
theorem internalContent_congr ...
theorem internalContent_union
    (h : Disjoint A B) :
    internalContent U (A ∪ B) =
      internalContent U A + internalContent U B
```

The content is then transported to the set ring of realized internal carriers:

```lean
def internalAddContent :
    MeasureTheory.AddContent ℝ≥0∞ internalSetRing

theorem internalAddContent_isSigmaSubadditive :
    internalAddContent U X |>.IsSigmaSubadditive
```

The exact constructors depend on ADR-0003. The stable user-facing declarations should
have shapes like:

```lean
def loebMeasurableSpace
    (U : Ultrafilter ι) (X : ι → Type*) :
    MeasurableSpace (Ultraproduct U X)

noncomputable def loebMeasure
    (U : Ultrafilter ι) (X : ι → Type*) :
    Measure (Ultraproduct U X)

theorem measurableSet_internal
    (A : InternalSet U X) :
    MeasurableSet[loebMeasurableSpace U X] A.carrier

@[simp] theorem loebMeasure_internal
    (A : InternalSet U X) :
    loebMeasure U X A.carrier = internalContent U A

instance : IsProbabilityMeasure (loebMeasure U X)
```

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

Required section API:

```lean
def section
    (s : Set (Fin (m + n) → Ω))
    (x : Fin m → Ω) :
    Set (Fin n → Ω)

theorem measurableSet_section ...
theorem measurable_sectionMeasure ...
theorem lintegral_sectionMeasure ...
theorem integral_section ...
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

- M0--M2 declaration names are provisional.
- Once a milestone gate is reached, renaming its public declarations requires a
  migration note and issue.
- Mathematical assumptions may never be hidden merely to preserve a provisional
  signature.
