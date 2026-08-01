/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Ultraproduct.Map

/-!
# The binary product equivalence for dependent filter products

A filter product of stagewise binary products is a binary product of filter products:

```
l.Product (fun i ↦ X i × Y i)  ≃  l.Product X × l.Product Y
```

This is the first equivalence of Layer U and the warm-up for the finite-power case: the
inverse must combine *two* representatives. Here that is done by nesting `liftOn`, so
the two representative changes are discharged one after another and no finiteness is
involved. U4 is the genuinely harder case, where the representatives are indexed by a
type and their eventual-equality sets must be intersected — which is where `Finite`
becomes necessary.

Both directions are built from the U1 eliminators, so `Quotient.mk`, `Quotient.sound`,
`Quotient.liftOn`, and `Filter.productSetoid` appear nowhere in this file. The
projections are stated against `Filter.Product.map`, the transport vocabulary from U2,
so downstream code never sees how a pair was rebuilt.

## Main results

* `Filter.Product.prodEquiv`: the equivalence, with `prodEquiv_ofFun` and
  `prodEquiv_symm_ofFun` computing both directions on representatives.
* `Filter.Product.fst_prodEquiv`, `snd_prodEquiv`: the components are the coordinate
  projections expressed as `map`.
* `Filter.Product.map_prodEquiv_symm`: transporting a pair through the inverse
  commutes with stagewise maps of each factor.

Everything is generic in `l : Filter ι`: no `Nonempty` fiber, ultrafilter, or
countable-incompleteness hypothesis, per ADR-0001.
-/

namespace Filter.Product

variable {ι : Type*} {l : Filter ι} {X : ι → Type*} {Y : ι → Type*}
  {Z : ι → Type*} {W : ι → Type*}

/-- Combine two filter-product elements into a product of the stagewise pairs. This is
the direction that must merge representatives: `liftOn` is nested, so the two
representative changes are discharged sequentially rather than through a single
combined eventual equality. -/
def mkPair (x : l.Product X) (y : l.Product Y) : l.Product fun i ↦ X i × Y i := by
  refine liftOn x (fun f ↦ liftOn y (fun g ↦ ofFun fun i ↦ (f i, g i)) ?_) ?_
  · exact fun _ _ h ↦ ofFun_congr (h.mono fun i hi ↦ by rw [hi])
  · intro f f' h
    induction y using Filter.Product.inductionOn with
    | _ g => exact ofFun_congr (h.mono fun i hi ↦ by rw [hi])

@[simp]
theorem mkPair_ofFun (f : (i : ι) → X i) (g : (i : ι) → Y i) :
    mkPair (ofFun f : l.Product X) (ofFun g) = ofFun fun i ↦ (f i, g i) :=
  rfl

/-- The binary product equivalence.

Simp discipline: the normal form computes on *representatives* (`prodEquiv_ofFun`,
`prodEquiv_symm_ofFun`), and round-trips are left to the generic
`Equiv.symm_apply_apply`/`apply_symm_apply`. A lemma rewriting `prodEquiv` or its
inverse *as a whole* on an arbitrary element — `prodEquiv_symm_apply`, or the
`@[simps! apply]`-generated form — must therefore not be `simp`: it pre-empts those and
leaves round-trip goals stuck. The projection lemmas `fst_prodEquiv`/`snd_prodEquiv`
are *not* affected, since they rewrite a component rather than the equivalence itself,
and are marked `simp`. -/
def prodEquiv : (l.Product fun i ↦ X i × Y i) ≃ l.Product X × l.Product Y where
  toFun x := (map (fun _ ↦ Prod.fst) x, map (fun _ ↦ Prod.snd) x)
  invFun p := mkPair p.1 p.2
  left_inv x := by
    induction x using Filter.Product.inductionOn with
    | _ f => simp
  right_inv p := by
    obtain ⟨x, y⟩ := p
    induction x, y using Filter.Product.inductionOn₂ with
    | _ f g => simp

@[simp]
theorem prodEquiv_ofFun (f : (i : ι) → X i × Y i) :
    prodEquiv (ofFun f : l.Product fun i ↦ X i × Y i)
      = (ofFun fun i ↦ (f i).1, ofFun fun i ↦ (f i).2) :=
  rfl

/-- Deliberately **not** a `simp` lemma: rewriting `prodEquiv.symm` into `mkPair` would
block the generic `Equiv.symm_apply_apply`/`apply_symm_apply` from closing round-trips.
Use it explicitly when the `mkPair` form is wanted. -/
theorem prodEquiv_symm_apply (p : l.Product X × l.Product Y) :
    prodEquiv.symm p = mkPair p.1 p.2 :=
  rfl

@[simp]
theorem prodEquiv_symm_ofFun (f : (i : ι) → X i) (g : (i : ι) → Y i) :
    (prodEquiv (l := l) (X := X) (Y := Y)).symm (ofFun f, ofFun g)
      = ofFun fun i ↦ (f i, g i) :=
  rfl

/-- The first component is the first coordinate projection, as a `map`. Safe as `simp`:
it rewrites a projection of the equivalence, not the equivalence itself, so the generic
round-trip lemmas are unaffected. -/
@[simp]
theorem fst_prodEquiv (x : l.Product fun i ↦ X i × Y i) :
    (prodEquiv x).1 = map (fun _ ↦ Prod.fst) x :=
  rfl

/-- The second component is the second coordinate projection, as a `map`. Safe as
`simp`, for the same reason as `fst_prodEquiv`. -/
@[simp]
theorem snd_prodEquiv (x : l.Product fun i ↦ X i × Y i) :
    (prodEquiv x).2 = map (fun _ ↦ Prod.snd) x :=
  rfl

/-- Naturality for the merging map: it commutes with stagewise maps of each factor. -/
theorem map_mkPair (f : (i : ι) → X i → Z i) (g : (i : ι) → Y i → W i)
    (x : l.Product X) (y : l.Product Y) :
    map (fun i (p : X i × Y i) ↦ (f i p.1, g i p.2)) (mkPair x y)
      = mkPair (map f x) (map g y) := by
  induction x, y using Filter.Product.inductionOn₂ with
  | _ a b => simp

/-- Naturality in equivalence form: transporting a pair through `prodEquiv.symm`
commutes with stagewise maps of each factor. This is the version downstream code should
use — it never mentions `mkPair`, so the rebuilding details stay hidden behind the
equivalence API. -/
@[simp]
theorem map_prodEquiv_symm (f : (i : ι) → X i → Z i) (g : (i : ι) → Y i → W i)
    (x : l.Product X) (y : l.Product Y) :
    map (fun i (p : X i × Y i) ↦ (f i p.1, g i p.2))
        ((prodEquiv (l := l) (X := X) (Y := Y)).symm (x, y))
      = (prodEquiv (l := l) (X := Z) (Y := W)).symm (map f x, map g y) := by
  simpa only [prodEquiv_symm_apply] using map_mkPair f g x y

/-! ### API tests -/

section Tests

/-- Both directions compute on representatives, with nothing quotient-shaped in the
goal. -/
example (f : (i : ι) → X i) (g : (i : ι) → Y i) :
    prodEquiv (ofFun fun i ↦ (f i, g i) : l.Product fun i ↦ X i × Y i)
      = (ofFun f, ofFun g) := by
  simp

/-- Round-trips are `simp`-provable in both directions, on arbitrary elements reached
through the public eliminators. -/
example (x : l.Product fun i ↦ X i × Y i) : prodEquiv.symm (prodEquiv x) = x := by
  simp

example (x : l.Product X) (y : l.Product Y) :
    prodEquiv (X := X) (Y := Y) (prodEquiv.symm (x, y)) = (x, y) := by
  simp

/-- Naturality is usable without ever naming `mkPair`: the rebuilding details stay
hidden behind the equivalence API. -/
example (f : (i : ι) → X i → Z i) (g : (i : ι) → Y i → W i)
    (x : l.Product X) (y : l.Product Y) :
    map (fun i (p : X i × Y i) ↦ (f i p.1, g i p.2))
        ((prodEquiv (l := l) (X := X) (Y := Y)).symm (x, y))
      = (prodEquiv (l := l) (X := Z) (Y := W)).symm (map f x, map g y) := by
  simp

/-- **Genuinely dependent families**, with both fibers varying with the index. -/
example (l : Filter ℕ) (f : (i : ℕ) → Fin (i + 1)) (g : (i : ℕ) → Fin (i + 2)) :
    prodEquiv (ofFun fun i ↦ (f i, g i) : l.Product fun i ↦ Fin (i + 1) × Fin (i + 2))
      = (ofFun f, ofFun g) := by
  simp

/-- **Independent universes** for the index and the two fiber families. -/
example {ι' : Type 2} {l' : Filter ι'} {X' : ι' → Type 5} {Y' : ι' → Type 7}
    (f : (i : ι') → X' i) (g : (i : ι') → Y' i) :
    prodEquiv (ofFun fun i ↦ (f i, g i) : l'.Product fun i ↦ X' i × Y' i)
      = (ofFun f, ofFun g) := by
  simp

end Tests

end Filter.Product
