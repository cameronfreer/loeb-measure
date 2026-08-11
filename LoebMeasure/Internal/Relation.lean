/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.Function
import LoebMeasure.Ultraproduct.Permutation

/-!
# Internal relations

An **internal relation** of arity `k` is an internal set on the stagewise `k`-th powers.
It is an *alias*, not a new structure.

## Which side the relation lives on

`InternalRelation U X k` is an internal set on `Ultraproduct U (fun i ↦ Fin k → X i)`,
**not** on `(Ultraproduct U X)^k`. That is deliberate and load-bearing: internality —
and later the Loeb measure — are defined on the ultraproduct-of-stagewise-powers side,
where a set is given by stagewise data. `Filter.Product.finPowerEquiv` appears only when
a relation is *realized* as a set of tuples, which is why that realization has its own
name, `tupleCarrier`, rather than overloading `InternalSet.carrier` — whose ambient type
is the ultraproduct of powers.

## Hypotheses

None: no nonempty fibers, no ultrafilter dichotomy, no properness, no countable
incompleteness.

## The end-to-end result

`comap` pulls a relation back along a coordinate selection, and under realization it
becomes an ordinary preimage of tuple sets:

```
tupleCarrier (R.comap σ) = (fun x ↦ x ∘ σ) ⁻¹' tupleCarrier R
```

This is where `Filter.Product.reindex_finPowerEquiv_symm` earns its keep — one of the
inverse-facing rules added because an audit predicted downstream goals would need them
— and it is the relation API the homomorphism-density slice at M4 will use.
-/

namespace Loeb

open Filter

variable {ι : Type*} {U : Ultrafilter ι} {X : ι → Type*} {k m n : ℕ}

/-- An internal relation of arity `k`: an internal set on the stagewise `k`-th powers.
Note the side: this is *not* a set of tuples of ultraproduct elements. -/
abbrev InternalRelation (U : Ultrafilter ι) (X : ι → Type*) (k : ℕ) :=
  InternalSet U fun i ↦ Fin k → X i

namespace InternalRelation

/-- The set of tuples of ultraproduct elements that a relation realizes.

Separately named from `InternalSet.carrier` because the ambient types differ: `carrier`
lives on the ultraproduct of powers, `tupleCarrier` on the power of the ultraproduct.
Transport between them is exactly `Filter.Product.finPowerEquiv`. -/
noncomputable def tupleCarrier (R : InternalRelation U X k) :
    Set (Fin k → Ultraproduct U X) :=
  (fun x ↦ (Filter.Product.finPowerEquiv (l := (U : Filter ι)) (X := X) k).symm x) ⁻¹'
    InternalSet.carrier R

@[simp]
theorem mem_tupleCarrier {R : InternalRelation U X k} {x : Fin k → Ultraproduct U X} :
    x ∈ tupleCarrier R ↔
      (Filter.Product.finPowerEquiv (l := (U : Filter ι)) (X := X) k).symm x
        ∈ InternalSet.carrier R :=
  Iff.rfl

/-- Pull a relation back along a coordinate selection: `σ` picks the `m` coordinates of
an `n`-tuple. This is a preimage along the internal map that precomposes with `σ`. -/
def comap (σ : Fin m → Fin n) (R : InternalRelation U X m) : InternalRelation U X n :=
  InternalSet.preimage
    (Filter.Product.ofFun fun _ (g : Fin n → X _) ↦ g ∘ σ : InternalMap U _ _) R

/-- The realized internal map of the coordinate selection is `Filter.Product.reindex`.

`private`: it is a statement about an anonymous implementation expression, and only
`carrier_comap` consumes it. If that internal map acquires a second consumer, give the
map itself a public name at that point. -/
private theorem toFun_reindexMap (σ : Fin m → Fin n) :
    InternalMap.toFun
        (Filter.Product.ofFun fun _ (g : Fin n → X _) ↦ g ∘ σ : InternalMap U _ _)
      = Filter.Product.reindex (l := (U : Filter ι)) (X := X) σ := by
  funext x
  induction x using Filter.Product.inductionOn with
  | _ x' => rfl

/-- **Coordinate pullback on the stagewise side** is reindexing. -/
@[simp]
theorem carrier_comap (σ : Fin m → Fin n) (R : InternalRelation U X m) :
    InternalSet.carrier (R.comap σ)
      = Filter.Product.reindex (l := (U : Filter ι)) (X := X) σ ⁻¹'
        InternalSet.carrier R := by
  rw [comap, InternalSet.carrier_preimage, toFun_reindexMap]

/-- **Coordinate pullback under realization is an ordinary tuple preimage.**

The end-to-end statement: internal coordinate pullbacks become preimages of tuple sets.
`Filter.Product.reindex_finPowerEquiv_symm` is what makes the two sides agree. -/
@[simp]
theorem tupleCarrier_comap (σ : Fin m → Fin n) (R : InternalRelation U X m) :
    tupleCarrier (R.comap σ) = (fun x : Fin n → Ultraproduct U X ↦ x ∘ σ) ⁻¹'
      tupleCarrier R := by
  ext x
  simp only [mem_tupleCarrier, carrier_comap, Set.mem_preimage,
    Filter.Product.reindex_finPowerEquiv_symm]

/-! ### API tests -/

section Tests

/-- Coordinate pullback on the stagewise side is reindexing. -/
example (σ : Fin m → Fin n) (R : InternalRelation U X m) :
    InternalSet.carrier (R.comap σ)
      = Filter.Product.reindex (l := (U : Filter ι)) (X := X) σ ⁻¹'
        InternalSet.carrier R := by
  simp

/-- **The end-to-end result**: under realization, a coordinate pullback is an ordinary
preimage of tuple sets. This is the shape M4's homomorphism-density argument needs. -/
example (σ : Fin m → Fin n) (R : InternalRelation U X m) :
    tupleCarrier (R.comap σ) = (fun x : Fin n → Ultraproduct U X ↦ x ∘ σ) ⁻¹'
      tupleCarrier R := by
  simp

/-- **A nontrivial coordinate selection**: a binary relation pulled back along a
selection of two coordinates from a triple — the shape M4 uses for an edge of a graph
inside a tuple of vertices. -/
example (σ : Fin 2 → Fin 3) (R : InternalRelation U X 2) (x : Fin 3 → Ultraproduct U X) :
    x ∈ tupleCarrier (R.comap σ) ↔ x ∘ σ ∈ tupleCarrier R := by
  simp

/-- **A genuinely dependent family.** -/
example (U : Ultrafilter ℕ) (R : InternalRelation U (fun i ↦ Fin (i + 1)) 1)
    (σ : Fin 1 → Fin 2) (x : Fin 2 → Ultraproduct U fun i ↦ Fin (i + 1)) :
    x ∈ tupleCarrier (R.comap σ) ↔ x ∘ σ ∈ tupleCarrier R := by
  simp

end Tests

end InternalRelation

end Loeb
