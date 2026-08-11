/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.Set
import LoebMeasure.Ultraproduct.Prod

/-!
# Internal maps and preimages

An **internal map** is a stagewise family of functions, taken up to eventual equality.
Its `toFun` is the function it realizes between ultraproducts, and `InternalSet.preimage`
pulls internal sets back along it.

As with `carrier`, quotient data and its interpretation are kept visibly separate: there
is no `CoeFun`, and `toFun` must be written. A coercion waits until a consumer shows it
improves the API.

## Hypotheses

Nothing here needs any: no nonempty fibers, no ultrafilter dichotomy, no properness, no
countable incompleteness.

No quotient reasoning is introduced either. Pointwise application is just another
consumer of `Filter.Product.map₂` — `toFun f = map₂ (fun _ f' x' ↦ f' x') f` — so
genericity comes structurally through the M1 abstraction rather than from a fresh lift
or a duplicated witness (contrast #47).

`carrier_preimage` in particular is the *same* eventual-membership proposition on both
sides — `x' i ∈ f' i ⁻¹' A' i` and `f' i (x' i) ∈ A' i` are the same statement — so it
needs no filter reasoning at all.
-/

namespace Loeb

open Filter

variable {ι : Type*} {U : Ultrafilter ι} {X Y Z : ι → Type*}

/-- An internal map: a stagewise family of functions, up to eventual equality. -/
abbrev InternalMap (U : Ultrafilter ι) (X Y : ι → Type*) :=
  (U : Filter ι).Product fun i ↦ X i → Y i

namespace InternalMap

/-- The function between ultraproducts that an internal map realizes. -/
def toFun (f : InternalMap U X Y) : Ultraproduct U X → Ultraproduct U Y :=
  Filter.Product.map₂ (fun _ f' x' ↦ f' x') f

@[simp]
theorem toFun_ofFun (f : (i : ι) → X i → Y i) (x : (i : ι) → X i) :
    toFun (Filter.Product.ofFun f : InternalMap U X Y) (Filter.Product.ofFun x)
      = Filter.Product.ofFun fun i ↦ f i (x i) :=
  rfl

/-- The internal identity map. -/
def id : InternalMap U X X := Filter.Product.ofFun fun _ ↦ _root_.id

/-- Composition of internal maps. -/
def comp (g : InternalMap U Y Z) (f : InternalMap U X Y) : InternalMap U X Z :=
  Filter.Product.map₂ (fun _ (g' : Y _ → Z _) (f' : X _ → Y _) ↦ g' ∘ f') g f

@[simp]
theorem comp_ofFun (g : (i : ι) → Y i → Z i) (f : (i : ι) → X i → Y i) :
    comp (Filter.Product.ofFun g : InternalMap U Y Z) (Filter.Product.ofFun f)
      = Filter.Product.ofFun fun i ↦ g i ∘ f i :=
  rfl

@[simp]
theorem toFun_id : toFun (id : InternalMap U X X) = _root_.id := by
  funext x
  induction x using Filter.Product.inductionOn with
  | _ x' => rfl

@[simp]
theorem toFun_comp (g : InternalMap U Y Z) (f : InternalMap U X Y) :
    toFun (g.comp f) = toFun g ∘ toFun f := by
  funext x
  induction g, f using Filter.Product.inductionOn₂ with
  | _ g' f' =>
    induction x using Filter.Product.inductionOn with
    | _ x' => rfl

end InternalMap

namespace InternalSet

/-- The preimage of an internal set along an internal map. -/
def preimage (f : InternalMap U X Y) (A : InternalSet U Y) : InternalSet U X :=
  Filter.Product.map₂ (fun _ (f' : X _ → Y _) (S : Set (Y _)) ↦ f' ⁻¹' S) f A

@[simp]
theorem preimage_ofFun (f : (i : ι) → X i → Y i) (A : (i : ι) → Set (Y i)) :
    preimage (Filter.Product.ofFun f : InternalMap U X Y) (Filter.Product.ofFun A)
      = Filter.Product.ofFun fun i ↦ f i ⁻¹' A i :=
  rfl

/-- **Preimage is realized by preimage.** No hypotheses: both sides are the same
eventual-membership proposition. -/
@[simp]
theorem carrier_preimage (f : InternalMap U X Y) (A : InternalSet U Y) :
    carrier (preimage f A) = InternalMap.toFun f ⁻¹' carrier A := by
  ext x
  induction x, f using Filter.Product.inductionOn₂ with
  | _ x' f' =>
    induction A using Filter.Product.inductionOn with
    | _ A' => rfl

@[simp]
theorem preimage_id (A : InternalSet U X) : preimage InternalMap.id A = A := by
  induction A using Filter.Product.inductionOn with
  | _ A' => rfl

theorem preimage_comp (g : InternalMap U Y Z) (f : InternalMap U X Y)
    (A : InternalSet U Z) :
    preimage (g.comp f) A = preimage f (preimage g A) := by
  induction g, f using Filter.Product.inductionOn₂ with
  | _ g' f' =>
    induction A using Filter.Product.inductionOn with
    | _ A' => rfl

end InternalSet

/-! ### API tests -/

namespace InternalMap

section Tests

/-- Realization computes on representatives. -/
example (f : (i : ι) → X i → Y i) (x : (i : ι) → X i) :
    toFun (Filter.Product.ofFun f : InternalMap U X Y) (Filter.Product.ofFun x)
      = Filter.Product.ofFun fun i ↦ f i (x i) := by
  simp

/-- Composition computes on representatives. -/
example (g : (i : ι) → Y i → Z i) (f : (i : ι) → X i → Y i) :
    comp (Filter.Product.ofFun g : InternalMap U Y Z) (Filter.Product.ofFun f)
      = Filter.Product.ofFun fun i ↦ g i ∘ f i := by
  simp

/-- Functoriality, by `simp`. -/
example (g : InternalMap U Y Z) (f : InternalMap U X Y) (x : Ultraproduct U X) :
    toFun (g.comp f) x = toFun g (toFun f x) := by
  simp

/-- Preimage is realized by preimage — the reason the seam exists. -/
example (f : InternalMap U X Y) (A : InternalSet U Y) :
    InternalSet.carrier (InternalSet.preimage f A) = toFun f ⁻¹' InternalSet.carrier A := by
  simp

/-- Preimage is functorial, contravariantly. -/
example (g : InternalMap U Y Z) (f : InternalMap U X Y) (A : InternalSet U Z) :
    InternalSet.preimage (g.comp f) A
      = InternalSet.preimage f (InternalSet.preimage g A) :=
  InternalSet.preimage_comp g f A

/-- **A genuinely dependent family**, with the map changing the fiber type. -/
example (U : Ultrafilter ℕ) (A : (i : ℕ) → Set ℕ) (x : (i : ℕ) → Fin (i + 1)) :
    (Filter.Product.ofFun x : Ultraproduct U fun i ↦ Fin (i + 1))
        ∈ InternalSet.carrier
          (InternalSet.preimage
            (Filter.Product.ofFun fun i (v : Fin (i + 1)) ↦ (v : ℕ))
            (Filter.Product.ofFun A))
      ↔ ∀ᶠ i in (U : Filter ℕ), ((x i : ℕ)) ∈ A i := by
  simp

end Tests

end InternalMap

end Loeb
