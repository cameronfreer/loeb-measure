/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Ultraproduct.Basic

/-!
# Coordinatewise maps of dependent filter products

A stagewise family of maps `f : (i : ι) → X i → Y i` induces a map of filter products.
This is the transport mechanism downstream constructions use instead of hand-rolled
quotient lifts: internal sets, internal functions, coordinate projections, and
reindexings are all `Filter.Product.map` of something.

`map` is defined through `Filter.Product.liftOn`, so `Quotient.liftOn` and
`Filter.productSetoid` appear nowhere, and `map_ofFun` is stated against the stable
`ofFun` head symbol established in `LoebMeasure/Ultraproduct/Basic.lean`.

## Main results

* `Filter.Product.map`: the induced map, with `map_ofFun` computing it on
  representatives.
* `Filter.Product.map_id`, `map_comp`, `map_map`: functoriality.
* `Filter.Product.map_congr`: `map` depends only on the eventual behaviour of the
  stagewise family.
* `Filter.Product.map_congr_apply`: the strictly sharper pointwise form — eventual
  agreement *at the given point* already suffices. This, rather than `map_congr`, is
  the interface later a.e.-style hypotheses will meet.

Everything is generic in `l : Filter ι`: no `Nonempty` fiber, ultrafilter, or
countable-incompleteness hypothesis, per ADR-0001.
-/

namespace Filter.Product

variable {ι : Type*} {l : Filter ι} {X : ι → Type*} {Y : ι → Type*} {Z : ι → Type*}

/-- The map of filter products induced by a stagewise family of maps. -/
def map (f : (i : ι) → X i → Y i) (x : l.Product X) : l.Product Y :=
  liftOn x (fun g ↦ ofFun fun i ↦ f i (g i))
    fun _ _ h ↦ ofFun_congr (h.mono fun i hi ↦ by rw [hi])

@[simp]
theorem map_ofFun (f : (i : ι) → X i → Y i) (x : (i : ι) → X i) :
    map f (ofFun x : l.Product X) = ofFun fun i ↦ f i (x i) :=
  rfl

@[simp]
theorem map_id : map (fun _ ↦ id) = (id : l.Product X → l.Product X) := by
  funext x
  induction x using Filter.Product.inductionOn with
  | _ g => simp

theorem map_id_apply (x : l.Product X) : map (fun _ ↦ id) x = x := by
  rw [map_id, id_eq]

theorem map_comp (f : (i : ι) → X i → Y i) (g : (i : ι) → Y i → Z i) :
    map (l := l) (fun i ↦ g i ∘ f i) = map g ∘ map f := by
  funext x
  induction x using Filter.Product.inductionOn with
  | _ h => simp [Function.comp_def]

/-- Composition, in applied form. -/
theorem map_map (f : (i : ι) → X i → Y i) (g : (i : ι) → Y i → Z i) (x : l.Product X) :
    map g (map f x) = map (fun i ↦ g i ∘ f i) x := by
  rw [map_comp]
  rfl

/-- `map` depends only on the eventual behaviour of the stagewise family. -/
theorem map_congr {f g : (i : ι) → X i → Y i} (h : ∀ᶠ i in l, f i = g i) :
    map (l := l) f = map g := by
  funext x
  induction x using Filter.Product.inductionOn with
  | _ k => exact ofFun_congr (h.mono fun i hi ↦ by rw [hi])

/-- The pointwise form of `map_congr`: agreeing eventually *at the given point* is
already enough. -/
theorem map_congr_apply {f g : (i : ι) → X i → Y i} (x : (i : ι) → X i)
    (h : ∀ᶠ i in l, f i (x i) = g i (x i)) :
    map f (ofFun x : l.Product X) = map g (ofFun x) :=
  ofFun_congr h

/-! ### API tests -/

section Tests

/-- Transport computes on representatives, and nothing in the goal mentions the
quotient implementation. -/
example (f : (i : ι) → X i → Y i) (x : (i : ι) → X i) :
    map f (ofFun x : l.Product X) = ofFun fun i ↦ f i (x i) := by simp

/-- Functoriality is usable by `simp` on an arbitrary element, reached through the
public eliminator. -/
example (f : (i : ι) → X i → Y i) (g : (i : ι) → Y i → Z i) (x : l.Product X) :
    map g (map f x) = map (fun i ↦ g i ∘ f i) x := by
  induction x using Filter.Product.inductionOn with
  | _ k => simp [Function.comp_def]

/-- **Genuinely dependent families**: the source and target fibers both vary with the
index, and the map changes the fiber type. -/
example (l : Filter ℕ) (x : (i : ℕ) → Fin (i + 1)) :
    map (fun i (v : Fin (i + 1)) ↦ (v : ℕ)) (ofFun x : l.Product fun i ↦ Fin (i + 1))
      = ofFun fun i ↦ (x i : ℕ) := by
  simp

/-- **Independent universes**, with the map crossing between them. -/
example {ι' : Type 2} {l' : Filter ι'} {X' : ι' → Type 5} {Y' : ι' → Type 7}
    (f : (i : ι') → X' i → Y' i) (x : (i : ι') → X' i) :
    map f (ofFun x : l'.Product X') = ofFun fun i ↦ f i (x i) := by
  simp

/-- Eventual agreement of the families suffices. -/
example {f g : (i : ι) → X i → Y i} (h : ∀ᶠ i in l, f i = g i) :
    map (l := l) f = map g :=
  map_congr h

end Tests

end Filter.Product
