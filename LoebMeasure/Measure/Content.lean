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

The stage measure is **fixed**: there is no stage-measure parameter and no generic
all-set evaluator. That is what ADR-0004 decided, and it is unaffected by how general
the stages themselves may be — a signature spike showed the measure-parameterized
version is not merely a wider definition, since its additivity needs the stagewise sets
to be *measurable*, which `InternalSet` deliberately does not record. General families
therefore arrive later as an addition, through a separate `InternalMeasurableSet` and a
parameterized content, rather than as a refactor of this layer.

The raw evaluator below turns out to make sense for **arbitrary measurable stages**, and
is stated that way rather than artificially restricted. Finiteness and discreteness
enter only where they are genuinely used, and not together: **finiteness** for
normalization and for additivity, **discreteness** for additivity alone. The *additive*
content — the one that becomes a measure — is what is restricted to finite discrete
stages.

## Exact stage hypotheses

C2 was specified with `[Fintype (X i)]` and `[MeasurableSingletonClass (X i)]`; **no C2
result needs either**, and the linter said so. C3's additivity does need
`MeasurableSingletonClass`. What each result actually takes:

| Result | Stage hypotheses |
| --- | --- |
| `internalContent`, `internalContent_ofFun`, `internalContent_bot` | `MeasurableSpace` only |
| `internalContent_le_one`, `internalContent_ne_top` | `MeasurableSpace` only |
| `internalContent_top` | `MeasurableSpace`, `Finite`, **`Nonempty`** |
| the private disjointness helper | **none** — purely Boolean |
| `internalContent_sup_of_disjoint` | `MeasurableSpace`, `Finite`, **`MeasurableSingletonClass`** |

Among the C2 results, finiteness appears only for normalization; the bound and the
finiteness of the content value require none, because `uniformOn` is
`IsZeroOrProbabilityMeasure` unconditionally and so `normalizedCounting_le_one` is
`prob_le_one` outright. `MeasurableSingletonClass` is not needed by any of them.

Additivity is where discreteness first earns its place: `measure_union` needs the
stagewise sets measurable, which on a finite discrete stage they are. Even there,
nonemptiness stays absent — additivity is about disjointness, not total mass.

**Nonemptiness appears only on `internalContent_top`**, which is the ADR-0002
distinction paying off: it is for *normalization*, never for boundedness. On an empty
stage the total mass is `0`, and the content of any internal set is `0` rather than
`∞`.

## Scope

The definition, its elementary values, and finite additivity. Transport to carriers,
the `MeasureTheory.AddContent` packaging, saturation, and the Carathéodory construction
are all downstream and deliberately absent.
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

omit [∀ i, Finite (X i)] in
/-- The content is a probability value. Needs **neither nonemptiness nor finiteness**:
`uniformOn` is `IsZeroOrProbabilityMeasure` unconditionally, and an empty stage
contributes `0` rather than `∞`. -/
theorem internalContent_le_one (A : InternalSet U X) : internalContent U A ≤ 1 := by
  induction A using Filter.Product.inductionOn with
  | _ A' =>
    exact ultralimit_le_one
      (Eventually.of_forall fun i ↦ normalizedCounting_le_one (A' i))

omit [∀ i, Finite (X i)] in
/-- **No accidental `∞`**, derived from the bound, and inheriting its lack of
hypotheses. -/
theorem internalContent_ne_top (A : InternalSet U X) : internalContent U A ≠ ∞ :=
  ((internalContent_le_one A).trans_lt (Ne.lt_top ENNReal.one_ne_top)).ne

omit [∀ i, Finite (X i)] in
/-- **The content is monotone.** Ordinary stagewise monotonicity of the stage measures,
transported by `Ultrafilter.ultralimit_mono`; the order on `InternalSet` unfolds to
eventual stagewise inclusion by `le_ofFun_iff`, so no ultrafilter property is used and
no nonemptiness or discreteness is needed. -/
@[gcongr]
theorem internalContent_mono {A B : InternalSet U X} (h : A ≤ B) :
    internalContent U A ≤ internalContent U B := by
  induction A, B using Filter.Product.inductionOn₂ with
  | _ A' B' =>
    rw [InternalSet.le_ofFun_iff] at h
    exact Ultrafilter.ultralimit_mono (h.mono fun i hi ↦ measure_mono hi)

omit [∀ i, Finite (X i)] in
/-- **The content is subadditive on joins.** Unlike `internalContent_sup_of_disjoint`
this is an *inequality*, and correspondingly cheaper: it is stagewise
`measure_union_le`, which needs no measurability of the stagewise sets and so no
discreteness — the reason it sits here among the elementary values rather than in the
additivity section below. -/
theorem internalContent_sup_le (A B : InternalSet U X) :
    internalContent U (A ⊔ B) ≤ internalContent U A + internalContent U B := by
  induction A, B using Filter.Product.inductionOn₂ with
  | _ A' B' =>
    rw [InternalSet.sup_ofFun, internalContent_ofFun, internalContent_ofFun,
      internalContent_ofFun, ← ultralimit_add]
    exact Ultrafilter.ultralimit_mono' fun i ↦ measure_union_le _ _

/-! ### Finite additivity

The first result making the content measure-like rather than merely bounded.

The two hypotheses do different jobs, and it is worth keeping them apart:
**disjointness** comes from the Boolean structure on `InternalSet` — `Disjoint A B`
unfolds through `disjoint_iff` and `inf_ofFun` to eventual stagewise disjointness, with
no mention of realized carriers — while **`MeasurableSingletonClass`** supplies
measurability of the finite stagewise subsets, which `measure_union` needs and which
disjointness does not provide.

No nonemptiness: additivity is about disjointness, not total mass. -/

omit [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)] in
/-- Disjoint internal sets are eventually disjoint stagewise. Proved through the
Boolean API alone: no carrier appears, and no measure-theoretic structure is used —
this is a fact about the Boolean algebra, not about measures.

`private`, and representative-specific: it is stated for `ofFun` arguments and has one
consumer. Should it acquire another, the right public form is an exact characterization
under `Loeb.InternalSet`, `disjoint_ofFun_iff`, rather than this one-directional
lemma. -/
private theorem eventually_disjoint_of_disjoint {A B : (i : ι) → Set (X i)}
    (h : Disjoint (Filter.Product.ofFun A : InternalSet U X) (Filter.Product.ofFun B)) :
    ∀ᶠ i in (U : Filter ι), Disjoint (A i) (B i) := by
  rw [disjoint_iff, InternalSet.inf_ofFun, InternalSet.bot_def,
    Filter.Product.ofFun_eq_ofFun] at h
  exact h.mono fun i hi ↦ Set.disjoint_iff_inter_eq_empty.2 hi

variable [∀ i, MeasurableSingletonClass (X i)]

/-- **The internal content is finitely additive.** -/
theorem internalContent_sup_of_disjoint {A B : InternalSet U X} (h : Disjoint A B) :
    internalContent U (A ⊔ B) = internalContent U A + internalContent U B := by
  induction A, B using Filter.Product.inductionOn₂ with
  | _ A' B' =>
    have hdisj := eventually_disjoint_of_disjoint h
    rw [InternalSet.sup_ofFun, internalContent_ofFun, internalContent_ofFun,
      internalContent_ofFun, ← ultralimit_add]
    refine Ultrafilter.ultralimit_congr (hdisj.mono fun i hi ↦ ?_)
    exact measure_union hi (Set.Finite.measurableSet (Set.toFinite _))

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

/-- **Finite additivity**, the C3 result. -/
example {A B : InternalSet U X} (h : Disjoint A B) :
    internalContent U (A ⊔ B) = internalContent U A + internalContent U B :=
  internalContent_sup_of_disjoint h

/-- Additivity on representatives. Note the hypothesis is still quotient-level
disjointness, which is *eventual* stagewise disjointness — not pointwise. -/
example (A B : (i : ι) → Set (X i))
    (h : Disjoint (Filter.Product.ofFun A : InternalSet U X) (Filter.Product.ofFun B)) :
    internalContent U (Filter.Product.ofFun A ⊔ Filter.Product.ofFun B)
      = internalContent U (Filter.Product.ofFun A : InternalSet U X)
        + internalContent U (Filter.Product.ofFun B) :=
  internalContent_sup_of_disjoint h

/-- A set and its complement partition the whole. A useful normalization corollary —
and, unlike additivity, it does need nonemptiness, through `internalContent_top`.

(Not a C4 input: `IsSetRing.addContent_of_union` needs the empty value and
disjoint-union additivity, not this.) -/
example [∀ i, Nonempty (X i)] (A : InternalSet U X) :
    internalContent U A + internalContent U Aᶜ = 1 := by
  rw [← internalContent_sup_of_disjoint disjoint_compl_right, sup_compl_eq_top,
    internalContent_top]

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
