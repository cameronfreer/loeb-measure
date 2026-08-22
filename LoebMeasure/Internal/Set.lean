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

The representation seam itself — `carrier` and `mem_carrier_ofFun` — uses **none** of
them: the identical descent elaborates verbatim over an arbitrary `Filter`, which is
how that claim was checked rather than assumed. `InternalSet` is nevertheless stated
for an `Ultrafilter`, matching where the project's mathematics lives, without those
proofs relying on it.

The two facts below then add hypotheses visibly, one at a time, rather than inheriting
them: `carrier_ofFun_nonempty_iff` takes nonempty fibers and nothing else, and
`carrier_injective` takes the dichotomy on top. Countable incompleteness appears
nowhere in this module.

## Scope

Deliberately narrow: the type, the carrier, the membership rule, and the two facts
making `carrier` faithful. The Boolean algebra and set ring, internal maps and
relations, and diagonalization are separate units. No coercion to `Set` is supplied,
and no derived extensionality lemma, until a second
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

/-- **A stagewise singleton realizes a singleton.** The carrier of the stagewise family
of singletons at `x` is exactly `{x}`, because eventual stagewise equality *is* equality
in the ultraproduct.

Needs no hypotheses at all — not nonemptiness, not the dichotomy — since it is
`Filter.Product.ofFun_eq_ofFun` read through the membership rule. It is what makes the
measure of a point computable from the stage measures without any approximation
argument. -/
@[simp]
theorem carrier_ofFun_singleton (x : (i : ι) → X i) :
    carrier (Filter.Product.ofFun fun i ↦ ({x i} : Set (X i)) : InternalSet U X)
      = {(Filter.Product.ofFun x : Ultraproduct U X)} := by
  ext y
  induction y using Filter.Product.inductionOn with
  | _ y' =>
    rw [Set.mem_singleton_iff, Filter.Product.ofFun_eq_ofFun, mem_carrier_ofFun]
    rfl

/-! ### Nonemptiness and injectivity

The two facts that make `carrier` a *faithful* embedding of internal-set data into
ordinary sets, which is what lets the Boolean algebra be stated against `Set`
operations.

Their hypotheses differ, and the difference is the point:

* `carrier_ofFun_nonempty_iff` uses nonempty fibers **only** to supply a default value
  outside the eventual good set. Its filter reasoning uses no ultrafilter property.
* `carrier_injective` additionally uses the **ultrafilter dichotomy**, and uses it in
  exactly one place — see its proof note.
* Neither uses countable incompleteness.

Nonemptiness is an explicit hypothesis `(hX : ∀ i, Nonempty (X i))` rather than an
instance, so the assumption boundary is visible in every statement that needs it. -/

/-- Choose a point in each of an eventually-nonempty family of stagewise sets.

This is where nonempty fibers are used, and all they are used for: a default value at
the stages outside the good set, whose behaviour is irrelevant. -/
private theorem exists_ofFun_mem (hX : ∀ i, Nonempty (X i)) {A : (i : ι) → Set (X i)}
    (h : ∀ᶠ i in (U : Filter ι), (A i).Nonempty) :
    ∃ x : (i : ι) → X i, ∀ᶠ i in (U : Filter ι), x i ∈ A i := by
  classical
  refine ⟨fun i ↦ if hi : (A i).Nonempty then hi.choose else (hX i).some, ?_⟩
  filter_upwards [h] with i hi
  simpa only [dif_pos hi] using hi.choose_spec

/-- **Carrier nonemptiness is stagewise-eventual nonemptiness.**

The forward direction needs no hypotheses at all; the reverse uses `hX` to default
outside the good set. No ultrafilter property is involved in either. -/
theorem carrier_ofFun_nonempty_iff (hX : ∀ i, Nonempty (X i))
    (A : (i : ι) → Set (X i)) :
    (carrier (Filter.Product.ofFun A : InternalSet U X)).Nonempty ↔
      ∀ᶠ i in (U : Filter ι), (A i).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    induction x using Filter.Product.inductionOn with
    | _ x' => exact ((mem_carrier_ofFun x' A).1 hx).mono fun _ hi ↦ ⟨_, hi⟩
  · intro h
    obtain ⟨x, hx⟩ := exists_ofFun_mem hX h
    exact ⟨Filter.Product.ofFun x, (mem_carrier_ofFun x A).2 hx⟩

/-- If one stagewise difference is eventually nonempty, the carriers differ: the
witness family lies eventually in one and eventually outside the other. -/
private theorem carrier_ofFun_ne (hX : ∀ i, Nonempty (X i))
    {A B : (i : ι) → Set (X i)}
    (h : ∀ᶠ i in (U : Filter ι), (A i \ B i).Nonempty) :
    carrier (Filter.Product.ofFun A : InternalSet U X)
      ≠ carrier (Filter.Product.ofFun B) := by
  obtain ⟨x, hx⟩ := exists_ofFun_mem hX h
  intro hEq
  have hA : (Filter.Product.ofFun x : Ultraproduct U X) ∈
      carrier (Filter.Product.ofFun A) :=
    (mem_carrier_ofFun x A).2 (hx.mono fun _ hi ↦ hi.1)
  have hB := (mem_carrier_ofFun x B).1 (hEq ▸ hA)
  obtain ⟨i, hi, hmem⟩ := (hx.and hB).exists
  exact hi.2 hmem

/-- **An internal set is determined by its carrier.**

Proof note — the one place the ultrafilter dichotomy is used, and why it is
unavoidable. Eventual stagewise *inequality* does not by itself yield a separating
point: the direction of the symmetric difference may vary by stage, and a witness
family must come from one consistent direction to be eventually inside one carrier and
eventually outside the other. The dichotomy selects that direction — deciding whether
`{i | (A i \ B i).Nonempty}` or its complement is large — before any witness is
chosen. -/
theorem carrier_injective (hX : ∀ i, Nonempty (X i)) :
    Function.Injective (carrier (U := U) (X := X)) := by
  intro A B hEq
  induction A, B using Filter.Product.inductionOn₂ with
  | _ A' B' =>
    rw [Filter.Product.ofFun_eq_ofFun]
    by_contra hne
    -- eventual inequality, then a *single* eventual direction for the difference
    have hne' : ∀ᶠ i in (U : Filter ι), A' i ≠ B' i := Ultrafilter.eventually_not.2 hne
    have hsplit : ∀ᶠ i in (U : Filter ι),
        (A' i \ B' i).Nonempty ∨ (B' i \ A' i).Nonempty := by
      filter_upwards [hne'] with i hi
      by_contra hcon
      push Not at hcon
      exact hi (Set.Subset.antisymm (Set.sdiff_eq_empty.1 hcon.1)
        (Set.sdiff_eq_empty.1 hcon.2))
    rcases Ultrafilter.eventually_or.1 hsplit with h | h
    · exact carrier_ofFun_ne hX h hEq
    · exact carrier_ofFun_ne hX h hEq.symm

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

/-- Nonemptiness transfers, by the stated rule. -/
example (hX : ∀ i, Nonempty (X i)) (A : (i : ι) → Set (X i))
    (h : ∀ᶠ i in (U : Filter ι), (A i).Nonempty) :
    (carrier (Filter.Product.ofFun A : InternalSet U X)).Nonempty :=
  (carrier_ofFun_nonempty_iff hX A).2 h

/-- Equal carriers force equal internal sets — the faithfulness I3 needs to state the
Boolean algebra against `Set` operations. -/
example (hX : ∀ i, Nonempty (X i)) (A B : InternalSet U X)
    (h : carrier A = carrier B) : A = B :=
  carrier_injective hX h

/-- **A genuinely dependent family**, for both new rules. -/
example (U : Ultrafilter ℕ) (A : (i : ℕ) → Set (Fin (i + 1)))
    (h : ∀ᶠ i in (U : Filter ℕ), (A i).Nonempty) :
    (carrier (Filter.Product.ofFun A : InternalSet U fun i ↦ Fin (i + 1))).Nonempty :=
  (carrier_ofFun_nonempty_iff (fun _ ↦ ⟨0⟩) A).2 h

/-- Carriers are ordinary sets, so ordinary set language applies to them — which is the
point of the seam. -/
example (A B : InternalSet U X) (h : ∀ x, x ∈ carrier A → x ∈ carrier B) :
    carrier A ⊆ carrier B :=
  h

end Tests

end InternalSet

end Loeb
