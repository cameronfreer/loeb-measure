/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.Set
import LoebMeasure.Ultraproduct.Map

/-!
# Internal singletons

Every point of the ultraproduct is internal: `InternalSet.singleton x` is the stagewise
family of singletons at `x`, and its carrier is exactly `{x}`.

## Why a separate module

`Internal/Set.lean` deliberately imports only `LoebMeasure.Basic`, keeping the
representation seam free of the functor layer. Defining `singleton` at the quotient level
needs `Filter.Product.map`, so it lives here rather than widening that import.

The representative-level computation `InternalSet.carrier_ofFun_singleton` stays in the
core module, where it needs nothing beyond the membership rule; `carrier_singleton` below
is its quotient-level face, and is the form downstream code should use.

## Hypotheses

None. `carrier_singleton` is `Filter.Product.ofFun_eq_ofFun` read through the membership
rule — eventual stagewise equality *is* equality in the ultraproduct — so no nonemptiness,
no ultrafilter dichotomy, and no countable incompleteness appear.

That is what makes the measure of a point computable directly from the stage measures,
with no approximation argument: see `Loeb.loebMeasure_singleton`.
-/

namespace Loeb

open Filter

variable {ι : Type*} {U : Ultrafilter ι} {X : ι → Type*}

namespace InternalSet

/-- The internal set of a point: stagewise, the singleton at each coordinate.

Defined by `Filter.Product.map` rather than by choosing a representative, so no quotient
constructor appears and the definition needs no hypotheses. -/
def singleton (x : Ultraproduct U X) : InternalSet U X :=
  Filter.Product.map (fun _ a ↦ ({a} : Set (X _))) x

@[simp]
theorem singleton_ofFun (x : (i : ι) → X i) :
    singleton (Filter.Product.ofFun x : Ultraproduct U X)
      = Filter.Product.ofFun fun i ↦ ({x i} : Set (X i)) :=
  Filter.Product.map_ofFun _ _

/-- **The carrier of an internal singleton is the singleton.**

The fact the measure layer consumes: a point of the ultraproduct is a realized internal
set, so results about internal sets apply to points with no approximation in between. -/
@[simp]
theorem carrier_singleton (x : Ultraproduct U X) : carrier (singleton x) = {x} := by
  induction x using Filter.Product.inductionOn with
  | _ x' => rw [singleton_ofFun, carrier_ofFun_singleton]

/-! ### API tests -/

section Tests

/-- The carrier rule fires by `simp`, with nothing quotient-shaped left. -/
example (x : Ultraproduct U X) : carrier (singleton x) = {x} := by simp

/-- A point is a member of its own internal set — the sanity check that the orientation
is right. -/
example (x : Ultraproduct U X) : x ∈ carrier (singleton x) := by simp

/-- **A genuinely dependent family.** -/
example (U : Ultrafilter ℕ) (x : Ultraproduct U fun i ↦ Fin (i + 1)) :
    carrier (singleton x) = {x} := by simp

/-- Distinct points give distinct internal sets, through the carrier — no injectivity
hypothesis needed, since the carriers are computed outright. -/
example (x y : Ultraproduct U X) (h : x ≠ y) : singleton x ≠ singleton y := fun hEq ↦
  h (Set.singleton_eq_singleton_iff.1 (by
    rw [← carrier_singleton x, ← carrier_singleton y, hEq]))

end Tests

end InternalSet

end Loeb
