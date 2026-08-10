/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.BooleanAlgebra
import Mathlib.MeasureTheory.SetAlgebra

/-!
# The realized carrier algebra

The subsets of the ultraproduct that are carriers of internal sets form an **algebra**
of sets — closed under complement as well as union — and therefore a **ring** of sets,
which is what `MeasureTheory.AddContent` consumes when the internal content is extended
at M3.

The algebra is proved first and the ring derived from it, since `IsSetAlgebra` needs
exactly `empty_mem`, `compl_mem`, and `union_mem`, and mathlib's
`IsSetAlgebra.isSetRing` supplies the rest.

This module is separate from `Internal/BooleanAlgebra.lean` so that the content-free
Boolean and diagonalization layers never import measure-theory packaging.

Closure needs only that a representing internal set **exists** for each carrier — not
that it is unique — so `carrier_injective` is not used here, and no nonempty-fibers
hypothesis appears. The ultrafilter dichotomy enters only through the carrier laws for
union and complement.
-/

namespace Loeb.InternalSet

open Filter MeasureTheory

variable {ι : Type*}
variable (U : Ultrafilter ι) (X : ι → Type*)

/-- The subsets of the ultraproduct realized by internal sets. -/
def carriers : Set (Set (Ultraproduct U X)) :=
  Set.range carrier

variable {U X}

@[simp]
theorem mem_carriers {s : Set (Ultraproduct U X)} :
    s ∈ carriers U X ↔ ∃ A : InternalSet U X, carrier A = s :=
  Iff.rfl

theorem carrier_mem_carriers (A : InternalSet U X) : carrier A ∈ carriers U X :=
  ⟨A, rfl⟩

/-- **The realized carriers form an algebra of sets.**

Each field is a carrier law from `Internal/BooleanAlgebra.lean` applied to the internal
sets that represent the given carriers; only their existence is used. -/
theorem isSetAlgebra_carriers : IsSetAlgebra (carriers U X) where
  empty_mem := ⟨⊥, carrier_bot⟩
  compl_mem := by
    rintro s ⟨A, rfl⟩
    exact ⟨Aᶜ, carrier_compl A⟩
  union_mem := by
    rintro s t ⟨A, rfl⟩ ⟨B, rfl⟩
    exact ⟨A ⊔ B, carrier_sup A B⟩

/-- The realized carriers form a ring of sets — the structure
`MeasureTheory.AddContent` consumes. -/
theorem isSetRing_carriers : IsSetRing (carriers U X) :=
  isSetAlgebra_carriers.isSetRing

end Loeb.InternalSet
