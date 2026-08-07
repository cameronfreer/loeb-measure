/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.Set
import LoebMeasure.Ultraproduct.Prod

/-!
# Boolean operations on internal sets

Internal sets carry the stagewise Boolean operations, and `carrier` preserves them.

## Where each fact's structure comes from

The operations themselves are `Filter.Product.map`/`map₂` of the corresponding `Set`
operations, so they and their representative computation rules use only ordinary
`Filter` API — no ultrafilter property, no nonempty fibers, no countable
incompleteness. The Boolean-algebra construction is likewise filter-generic; the public
`BooleanAlgebra` instance is scoped to `InternalSet U X` rather than installed on
`Filter.Product`, since a generic public instance is a broader upstream decision with
coherence implications (see #45).

The theorems saying `carrier` *preserves* the operations are where the structure
stratifies, and the pattern is not uniform:

| Fact | Consumes |
| --- | --- |
| `carrier_bot` | properness — supplied by `Ultrafilter` |
| `carrier_top`, `carrier_inf` | ordinary filter laws only |
| `carrier_sup`, `carrier_compl` | the **ultrafilter dichotomy** |
| `carrier_sdiff`, `carrier_symmDiff` | derived from those |

Nothing here uses nonempty fibers or countable incompleteness, and **`carrier_injective`
is deliberately not used**: set-ring closure needs only that representing internal sets
*exist*. Proving these laws through injectivity would drag its nonempty-fibers
hypothesis into statements that hold for arbitrary fibers. Injectivity becomes
load-bearing later, at content transport.
-/

namespace Loeb.InternalSet

open Filter

variable {ι : Type*} {U : Ultrafilter ι} {X : ι → Type*}

/-! ### Operations -/

instance : Bot (InternalSet U X) := ⟨Filter.Product.ofFun fun _ ↦ ∅⟩
instance : Top (InternalSet U X) := ⟨Filter.Product.ofFun fun _ ↦ Set.univ⟩
instance : Compl (InternalSet U X) := ⟨Filter.Product.map fun _ ↦ compl⟩
instance : Max (InternalSet U X) := ⟨Filter.Product.map₂ fun _ ↦ (· ∪ ·)⟩
instance : Min (InternalSet U X) := ⟨Filter.Product.map₂ fun _ ↦ (· ∩ ·)⟩
instance : SDiff (InternalSet U X) := ⟨Filter.Product.map₂ fun _ ↦ (· \ ·)⟩

@[simp] theorem bot_def : (⊥ : InternalSet U X) = Filter.Product.ofFun fun _ ↦ ∅ := rfl
@[simp] theorem top_def :
    (⊤ : InternalSet U X) = Filter.Product.ofFun fun _ ↦ Set.univ := rfl

@[simp]
theorem compl_ofFun (A : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun A : InternalSet U X)ᶜ = Filter.Product.ofFun fun i ↦ (A i)ᶜ :=
  rfl

@[simp]
theorem sup_ofFun (A B : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun A : InternalSet U X) ⊔ Filter.Product.ofFun B
      = Filter.Product.ofFun fun i ↦ A i ∪ B i :=
  rfl

@[simp]
theorem inf_ofFun (A B : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun A : InternalSet U X) ⊓ Filter.Product.ofFun B
      = Filter.Product.ofFun fun i ↦ A i ∩ B i :=
  rfl

@[simp]
theorem sdiff_ofFun (A B : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun A : InternalSet U X) \ Filter.Product.ofFun B
      = Filter.Product.ofFun fun i ↦ A i \ B i :=
  rfl

/-! ### Carriers of the operations

This is where the ultrafilter structure enters, and only here. Each statement records
what it consumes. -/

/-- The empty internal set has empty carrier. Uses **properness** — a point of the
carrier would make `∅` eventually inhabited — which `Ultrafilter` supplies. -/
@[simp]
theorem carrier_bot : carrier (⊥ : InternalSet U X) = ∅ := by
  ext x
  induction x using Filter.Product.inductionOn with
  | _ x' =>
    simp only [bot_def, mem_carrier_ofFun, Set.mem_empty_iff_false, iff_false]
    exact fun h ↦ h.exists.elim fun _ hi ↦ hi

/-- The full internal set has full carrier. Ordinary filter laws only. -/
@[simp]
theorem carrier_top : carrier (⊤ : InternalSet U X) = Set.univ := by
  ext x
  induction x using Filter.Product.inductionOn with
  | _ x' => simp

/-- Intersection is preserved. Ordinary filter laws only: `∀ᶠ` distributes over `∧`. -/
@[simp]
theorem carrier_inf (A B : InternalSet U X) :
    carrier (A ⊓ B) = carrier A ∩ carrier B := by
  ext x
  induction x, A using Filter.Product.inductionOn₂ with
  | _ x' A' =>
    induction B using Filter.Product.inductionOn with
    | _ B' => simp [Filter.eventually_and]

/-- Union is preserved. Uses the **ultrafilter dichotomy**: an eventual disjunction
splits into a disjunction of eventual statements, which is false for a general
filter. -/
@[simp]
theorem carrier_sup (A B : InternalSet U X) :
    carrier (A ⊔ B) = carrier A ∪ carrier B := by
  ext x
  induction x, A using Filter.Product.inductionOn₂ with
  | _ x' A' =>
    induction B using Filter.Product.inductionOn with
    | _ B' => simpa using Ultrafilter.eventually_or

/-- Complement is preserved. Uses the **ultrafilter dichotomy** via
`Ultrafilter.eventually_not`. -/
@[simp]
theorem carrier_compl (A : InternalSet U X) : carrier Aᶜ = (carrier A)ᶜ := by
  ext x
  induction x, A using Filter.Product.inductionOn₂ with
  | _ x' A' =>
    simp only [compl_ofFun, mem_carrier_ofFun, Set.mem_compl_iff]
    exact Ultrafilter.eventually_not

/-- Difference is preserved, derived from complement and intersection. -/
@[simp]
theorem carrier_sdiff (A B : InternalSet U X) :
    carrier (A \ B) = carrier A \ carrier B := by
  ext x
  induction x, A using Filter.Product.inductionOn₂ with
  | _ x' A' =>
    induction B using Filter.Product.inductionOn with
    | _ B' =>
      simp only [sdiff_ofFun, mem_carrier_ofFun, Set.mem_sdiff, Filter.eventually_and]
      exact and_congr_right fun _ ↦ Ultrafilter.eventually_not

/-! ### API tests -/

section Tests

/-- Operations compute on representatives. -/
example (A B : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun A : InternalSet U X) ⊔ Filter.Product.ofFun B
      = Filter.Product.ofFun fun i ↦ A i ∪ B i := by
  simp

/-- The carrier laws fire by `simp`, so downstream reasoning happens in ordinary set
language. -/
example (A B : InternalSet U X) :
    carrier (A ⊓ B) ∪ carrier (A \ B) = (carrier A ∩ carrier B) ∪ (carrier A \ carrier B) := by
  simp

/-- **A genuinely dependent family.** -/
example (U : Ultrafilter ℕ) (A B : (i : ℕ) → Set (Fin (i + 1))) :
    carrier ((Filter.Product.ofFun A : InternalSet U fun i ↦ Fin (i + 1))
        ⊔ Filter.Product.ofFun B)
      = carrier (Filter.Product.ofFun A : InternalSet U fun i ↦ Fin (i + 1))
        ∪ carrier (Filter.Product.ofFun B) :=
  carrier_sup _ _

end Tests

end Loeb.InternalSet
