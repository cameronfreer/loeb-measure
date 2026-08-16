/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.BooleanAlgebra
import LoebMeasure.Measure.Counting
import LoebMeasure.Ultralimit.Probability

/-!
# Internal content

The content of an internal set: the ultralimit of its stagewise normalized counting
values. This is where the measure layer first meets internal-set data.

## Counting-first, per ADR-0004

The stages are finite and discrete, and the stage measure is fixed — there is **no
stage-measure parameter** and no generic all-set evaluator. A signature spike showed the
general measured-family version is not merely a wider definition: its additivity needs
the stagewise sets to be *measurable*, which `InternalSet` deliberately does not record.
General families therefore arrive later as an addition, through a separate
`InternalMeasurableSet` and a parameterized content, rather than as a refactor of this
layer.

## Exact stage hypotheses

The unit was specified with `[Fintype (X i)]` and `[MeasurableSingletonClass (X i)]`;
neither is needed, and the linter said so. What each result actually takes:

| Result | Stage hypotheses |
| --- | --- |
| `internalContent`, `internalContent_ofFun`, `internalContent_bot` | `MeasurableSpace` only |
| `internalContent_le_one`, `internalContent_ne_top` | `MeasurableSpace`, `Finite` |
| `internalContent_top` | `MeasurableSpace`, `Finite`, **`Nonempty`** |

`Finite` rather than `Fintype`, because nothing here enumerates a stage; and no
`MeasurableSingletonClass`, because the bound comes from `normalizedCounting_le_one` —
which is `prob_le_one` on a nonempty stage — rather than from the cardinality formula.

**Nonemptiness appears only on `internalContent_top`**, which is the ADR-0002
distinction paying off: it is for *normalization*, never for boundedness. On an empty
stage the total mass is `0`, and the content of any internal set is `0` rather than
`∞`.

## Scope

The definition and its elementary values. Additivity, transport to carriers, the
`MeasureTheory.AddContent` packaging, saturation, and the Carathéodory construction are
all downstream and deliberately absent.
-/

namespace Loeb

open Filter MeasureTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]

/-- The internal content of an internal set: the ultralimit of its stagewise normalized
counting values.

Descends through `Filter.Product.liftOn`; the well-definedness obligation is exactly
`Ultrafilter.ultralimit_congr` applied to the eventual equality of representatives, so
no quotient argument appears. -/
noncomputable def internalContent (U : Ultrafilter ι) (A : InternalSet U X) : ℝ≥0∞ :=
  Filter.Product.liftOn A
    (fun A' ↦ U.ultralimit fun i ↦ normalizedCounting (X i) (A' i))
    (fun _ _ h ↦ Ultrafilter.ultralimit_congr (h.mono fun _ hi ↦ by simp only [hi]))

variable {U : Ultrafilter ι}

omit [∀ i, Finite (X i)] in
@[simp]
theorem internalContent_ofFun (A : (i : ι) → Set (X i)) :
    internalContent U (Filter.Product.ofFun A : InternalSet U X)
      = U.ultralimit fun i ↦ normalizedCounting (X i) (A i) :=
  rfl

omit [∀ i, Finite (X i)] in
/-- The empty internal set has content zero. Needs neither nonemptiness nor, as it
turns out, finiteness or discreteness of the stages: the stagewise value is the measure
of `∅`. -/
@[simp]
theorem internalContent_bot : internalContent U (⊥ : InternalSet U X) = 0 := by
  simp

/-- **The full internal set has content one — and this is the only result needing
nonempty stages.** On an empty stage the total mass is `0`, not `1`. -/
@[simp]
theorem internalContent_top [∀ i, Nonempty (X i)] :
    internalContent U (⊤ : InternalSet U X) = 1 := by
  simp

/-- The content is a probability value. **No nonemptiness**: an empty stage contributes
`0`, not `∞`. -/
theorem internalContent_le_one (A : InternalSet U X) : internalContent U A ≤ 1 := by
  induction A using Filter.Product.inductionOn with
  | _ A' =>
    exact ultralimit_le_one
      (Eventually.of_forall fun i ↦ normalizedCounting_le_one (A' i))

/-- **No accidental `∞`**, derived from the bound. -/
theorem internalContent_ne_top (A : InternalSet U X) : internalContent U A ≠ ∞ :=
  ((internalContent_le_one A).trans_lt (Ne.lt_top ENNReal.one_ne_top)).ne

/-! ### API tests -/

section Tests

/-- The content computes on representatives. -/
example (A : (i : ι) → Set (X i)) :
    internalContent U (Filter.Product.ofFun A : InternalSet U X)
      = U.ultralimit fun i ↦ normalizedCounting (X i) (A i) := by
  simp

/-- Elementary values, by `simp`. -/
example [∀ i, Nonempty (X i)] :
    internalContent U (⊥ : InternalSet U X) = 0
      ∧ internalContent U (⊤ : InternalSet U X) = 1 := by
  simp

/-- The bound holds with no nonemptiness hypothesis in sight. -/
example (A : InternalSet U X) : internalContent U A ≤ 1 ∧ internalContent U A ≠ ∞ :=
  ⟨internalContent_le_one A, internalContent_ne_top A⟩

/-- **A genuinely dependent family**: the stage spaces vary with the index. -/
example (U : Ultrafilter ℕ) (A : (i : ℕ) → Set (Fin (i + 1))) :
    internalContent U (Filter.Product.ofFun A : InternalSet U fun i ↦ Fin (i + 1)) ≤ 1 :=
  internalContent_le_one _

/-- The bound survives *empty* stages, where a careless normalization would give `∞`.
This is what makes the nonemptiness split load-bearing rather than cosmetic. -/
example (U : Ultrafilter ℕ) (A : (i : ℕ) → Set (Fin i)) :
    internalContent U (Filter.Product.ofFun A : InternalSet U fun i ↦ Fin i) ≤ 1 :=
  internalContent_le_one _

end Tests

end Loeb
