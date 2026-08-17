/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.SetRing
import LoebMeasure.Measure.Content
import Mathlib.MeasureTheory.Measure.AddContent

/-!
# Packaging the internal content as an `AddContent`

(The module is `Packaging` rather than `AddContent`, which would shadow mathlib's
`MeasureTheory.AddContent` inside this namespace.)

The internal content, transported from internal sets to the subsets of the ultraproduct
they realize, and packaged as a `MeasureTheory.AddContent` on `InternalSet.carriers` —
the object the Carathéodory extension consumes.

## Where nonemptiness enters, and why it is new

`(hX : ∀ i, Nonempty (X i))` is an **explicit argument**, not an instance, matching
`InternalSet.carrier_injective` and keeping its role visible.

This is the first place carrier injectivity is genuinely load-bearing. Every earlier use
was avoidable: I3's Boolean laws are proved through representatives, and C3's
disjointness comes from the Boolean structure rather than from carriers.

What injectivity supplies is precise. The transported function is well defined without
it — it simply chooses *some* representing internal set. What fails without injectivity
is that it **factors `internalContent` through `carrier` representation-independently**:
the chosen internal set need not be the one written, and only faithfulness makes the two
values agree.

Note precisely what nonemptiness is and is not used for. It appears twice, both times
for **faithfulness**, never for additivity:

* in `transported_carrier`, so the representing internal set chosen by the definition
  agrees with the one written;
* in the additivity obligation, to convert *carrier-level* disjointness back into
  disjointness of internal sets — again `carrier_injective`, read in the other
  direction.

The additivity itself is C3's `internalContent_sup_of_disjoint`, which carries no
nonemptiness hypothesis at all. So the hypothesis is doing transport work in both
places, and none of the measure-theoretic work.

## Values off the carriers

The underlying function is defined on all of `Set (Ultraproduct U X)`, and an
`AddContent` can indeed be *evaluated* anywhere. What is confined to the ring are its
**laws** and everything downstream: `AddContent`'s additivity obligations quantify over
members of `InternalSet.carriers U X`, and the Carathéodory extension reads only those
values. Off the ring the function returns `0` by an arbitrary convention, and no result
here or later may depend on that choice.

## Scope

The transport and its packaging. Saturation, continuity at `∅`, σ-subadditivity, outer
measures, and the Carathéodory construction are all C5 onward and deliberately absent.
-/

namespace Loeb

open Filter MeasureTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] {U : Ultrafilter ι}

open Classical in
/-- The internal content transported to subsets of the ultraproduct.

Only the values on `InternalSet.carriers U X` are meaningful; off that family this
returns `0` by convention, and no result below depends on that choice.

The *definition* needs no nonemptiness — it picks some representing internal set. It is
`transported_carrier`, which says the choice does not matter, that needs
`carrier_injective` and hence nonemptiness. -/
private noncomputable def transported (s : Set (Ultraproduct U X)) : ℝ≥0∞ :=
  if h : s ∈ InternalSet.carriers U X then internalContent U h.choose else 0

omit [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
/-- **The transported value on a carrier is the content.** This is where
`carrier_injective` does its work: the internal set chosen to represent the carrier need
not be the one written, so faithfulness is what makes the two agree. -/
private theorem transported_carrier (hX : ∀ i, Nonempty (X i)) (A : InternalSet U X) :
    transported (InternalSet.carrier A) = internalContent U A := by
  have hmem : InternalSet.carrier A ∈ InternalSet.carriers U X := ⟨A, rfl⟩
  rw [transported, dif_pos hmem]
  congr 1
  exact InternalSet.carrier_injective hX hmem.choose_spec

omit [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
private theorem transported_empty (hX : ∀ i, Nonempty (X i)) :
    transported (U := U) (X := X) ∅ = 0 := by
  have h : (∅ : Set (Ultraproduct U X)) = InternalSet.carrier (⊥ : InternalSet U X) :=
    InternalSet.carrier_bot.symm
  rw [h, transported_carrier hX, internalContent_bot]

/-- **The internal content as an additive content on the realized carriers.**

Built by `MeasureTheory.IsSetRing.addContent_of_union` from exactly two inputs: the
empty value, and additivity on disjoint members — the latter being C3's
`internalContent_sup_of_disjoint` after transport. No finite-union induction is
performed here; the constructor supplies it. -/
noncomputable def internalAddContent (hX : ∀ i, Nonempty (X i)) :
    AddContent ℝ≥0∞ (InternalSet.carriers U X) :=
  InternalSet.isSetRing_carriers.addContent_of_union transported (transported_empty hX)
    (by
      rintro s t ⟨A, rfl⟩ ⟨B, rfl⟩ hdisj
      have hAB : Disjoint A B := by
        rw [disjoint_iff] at hdisj ⊢
        refine InternalSet.carrier_injective hX ?_
        rw [InternalSet.carrier_inf, InternalSet.carrier_bot,
          ← Set.disjoint_iff_inter_eq_empty]
        exact Set.disjoint_iff_inter_eq_empty.2 hdisj
      rw [← InternalSet.carrier_sup, transported_carrier hX, transported_carrier hX,
        transported_carrier hX, internalContent_sup_of_disjoint hAB])

/-- Evaluation of the packaged content on a carrier. -/
@[simp]
theorem internalAddContent_carrier (hX : ∀ i, Nonempty (X i)) (A : InternalSet U X) :
    internalAddContent hX (InternalSet.carrier A) = internalContent U A :=
  transported_carrier hX A

/-! ### API tests -/

section Tests

/-- **The interface C5 needs**: an `AddContent` on the realized carriers, evaluating to
the internal content. -/
example (hX : ∀ i, Nonempty (X i)) (A : InternalSet U X) :
    internalAddContent (U := U) hX (InternalSet.carrier A) = internalContent U A := by
  simp

/-- Its empty value, which `addContent_of_union` consumed. -/
example (hX : ∀ i, Nonempty (X i)) :
    internalAddContent (U := U) (X := X) hX ∅ = 0 := by
  simp

/-- Additivity comes for free from the constructor, on members of the ring. -/
example (hX : ∀ i, Nonempty (X i)) (A B : InternalSet U X)
    (h : Disjoint (InternalSet.carrier A) (InternalSet.carrier B)) :
    internalAddContent (U := U) hX (InternalSet.carrier A ∪ InternalSet.carrier B)
      = internalAddContent hX (InternalSet.carrier A)
        + internalAddContent hX (InternalSet.carrier B) :=
  addContent_union InternalSet.isSetRing_carriers ⟨A, rfl⟩ ⟨B, rfl⟩ h

/-- **A genuinely dependent family.** -/
example (U : Ultrafilter ℕ) (hX : ∀ i, Nonempty (Fin (i + 1)))
    (A : InternalSet U fun i ↦ Fin (i + 1)) :
    internalAddContent (U := U) hX (InternalSet.carrier A) = internalContent U A := by
  simp

end Tests

end Loeb
