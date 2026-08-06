/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Basic

/-!
# Internal sets and their carriers

An **internal set** is a stagewise family of subsets, taken up to eventual equality: an
element of the dependent filter product of the powersets. Its **carrier** is an honest
`Set` of the ultraproduct, and membership in the carrier is eventual membership
stagewise:

```
x ∈ A.carrier  ↔  ∀ᶠ i in U, x i ∈ A i
```

This is the representation seam the measure layer rests on. Everything downstream —
the Boolean algebra, the set ring, internal content — is phrased against `carrier`, so
that measure theory can be written in ordinary `Set` and `MeasurableSet` language while
the stagewise data stays computational.

## Hypothesis separation

The carrier and its membership rule need **nothing** beyond the filter structure: no
nonempty fibers, no ultrafilter property, and no countable incompleteness. The descent
is a nested `Filter.Product.liftOn` over the internal-set representative and the point
representative, and both well-definedness obligations are ordinary eventual-equality
congruences.

That matters because M2 is where three easily-conflated hypotheses arrive, and
ADR-0001 requires them to stay apart:

* **nonempty fibers** — for choosing a stagewise *witness* or default value in later
  nonemptiness and diagonal arguments. Not for quotient representatives, which need no
  such hypothesis, as this module demonstrates;
* **the ultrafilter dichotomy** — for passing from `A ≠ ∅` at the quotient level to
  *eventual* nonemptiness, and for carrier injectivity;
* **countable incompleteness** — for diagonalization, and only there.

This module uses none of them, which is the cleanest possible base for keeping them
separate. `InternalSet` is nevertheless stated for an `Ultrafilter`, matching where the
project's mathematics lives, without the proofs relying on it: the identical descent
elaborates verbatim over an arbitrary `Filter`, which is how that claim was checked
rather than assumed.

## Scope

Deliberately narrow: the type, the carrier, and the membership rule. The Boolean
algebra and set ring, carrier injectivity, internal maps and relations, and
diagonalization are separate units. No coercion to `Set` is supplied until a second
consumer justifies one; the named `carrier` keeps statements readable in the meantime.
-/

namespace Loeb

open Filter

variable {ι : Type*} {U : Ultrafilter ι} {X : ι → Type*}

/-- An internal set: a stagewise family of subsets, up to eventual equality.

This quantifies over **all** stagewise subsets, deliberately. For the initial model —
normalized counting measure on finite types — every stagewise set is measurable, so
nothing is lost; general measured families will add a separate internal *measurable*
set type with a forgetful map to this one, which puts the generalization cost in the
domain of the content rather than in this layer. -/
abbrev InternalSet (U : Ultrafilter ι) (X : ι → Type*) :=
  (U : Filter ι).Product fun i ↦ Set (X i)

namespace InternalSet

/-- The subset of the ultraproduct that an internal set denotes.

Defined by descending over both representatives with `Filter.Product.liftOn`, so no
quotient constructor appears and no ultrafilter property is used. -/
def carrier (A : InternalSet U X) : Set (Ultraproduct U X) :=
  Filter.Product.liftOn A
    (fun A' x ↦
      Filter.Product.liftOn x (fun x' ↦ ∀ᶠ i in (U : Filter ι), x' i ∈ A' i)
        (fun _ _ h ↦ propext (eventually_congr (h.mono fun _ hi ↦ by rw [hi]))))
    (fun _ _ h ↦ by
      funext x
      induction x using Filter.Product.inductionOn with
      | _ x' => exact propext (eventually_congr (h.mono fun _ hi ↦ by rw [hi])))

/-- **Membership is eventual membership.** The characterization the whole layer is
built on. -/
@[simp]
theorem mem_carrier_ofFun (x : (i : ι) → X i) (A : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun x : Ultraproduct U X) ∈ carrier (Filter.Product.ofFun A) ↔
      ∀ᶠ i in (U : Filter ι), x i ∈ A i :=
  Iff.rfl

/-! ### API tests -/

section Tests

/-- The membership rule fires by `simp`, with nothing quotient-shaped in the goal. -/
example (x : (i : ι) → X i) (A : (i : ι) → Set (X i))
    (h : ∀ᶠ i in (U : Filter ι), x i ∈ A i) :
    (Filter.Product.ofFun x : Ultraproduct U X) ∈ carrier (Filter.Product.ofFun A) := by
  simp [h]

/-- **A genuinely dependent family**: the ambient types vary with the index. -/
example (U : Ultrafilter ℕ) (x : (i : ℕ) → Fin (i + 1))
    (A : (i : ℕ) → Set (Fin (i + 1)))
    (h : ∀ᶠ i in (U : Filter ℕ), x i ∈ A i) :
    (Filter.Product.ofFun x : Ultraproduct U fun i ↦ Fin (i + 1))
      ∈ carrier (Filter.Product.ofFun A) := by
  simp [h]

/-- Carriers are ordinary sets, so ordinary set language applies to them — which is the
point of the seam. -/
example (A B : InternalSet U X) (h : ∀ x, x ∈ carrier A → x ∈ carrier B) :
    carrier A ⊆ carrier B :=
  h

end Tests

end InternalSet

end Loeb
