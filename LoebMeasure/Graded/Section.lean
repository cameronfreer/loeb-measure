/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Graded.Power
import LoebMeasure.Graded.Split
import LoebMeasure.Integral.Measurable

/-!
# Exact internal sections and section-content functions

For an internal relation `R` of arity `m + n` and a tuple `x : Fin m → Ultraproduct U X`,
the **section** of `R` at `x` is an internal relation of arity `n`, and its realization is
exactly the algebraic section of the realized tuple set:

```
tupleCarrier (R.sectionAt x) = Graded.sectionAt (tupleCarrier R) x
```

Exactly, not almost everywhere: every section of an internal set is internal. That is the
starting point for Fubini, and it is the distinction between this module and P6's
almost-everywhere sections of arbitrary Loeb-measurable sets, which completion does not
allow to be internal in general.

## The construction

`x` is assembled on the stagewise side through `(realize m).symm`, and the section is
`Filter.Product.map₂` of the stagewise section operation applied to that assembly and to
`R`. No representative is chosen and no fresh quotient lift is written; the representative
computation rule `sectionAt_ofFun` is `map₂_ofFun`. The construction and the carrier
identity need **no stage structure at all**: not measurability, not finiteness, not
nonemptiness, and not `hU`.

The carrier identity rests on one compatibility between the realization and the canonical
split, `realize_splitMap`, proved through M1's coordinate API — `Fin.addCases` on the
combined coordinate, then the coordinate rules of the split and of the realization — and
never by unfolding `Fin.appendEquiv`.

## The function P5 will integrate

`sectionContent R x` is the internal content of the section at `x`: an `ℝ≥0∞`-valued
function on `Fin m → Ultraproduct U X`. To show it measurable, it is exposed as a lift.
`sectionContentMap R` is the real-valued internal map on the stagewise `m`-powers
represented by

```
a ↦ (normalizedCounting (Fin n → X i) {b | splitEquiv (X i) m n (a, b) ∈ R i}).toReal
```

built by `Filter.Product.map` on `R`. It is uniformly bounded by `1`, and its lift at
`(realize m).symm x` is the real section content, `lift_sectionContentMap`. Stage
`MeasurableSpace` alone suffices for all of that. The measurability theorem then adds the
finite discrete stage structure and **left**-power nonemptiness, and is M5's
`measurable_lift` composed with P2's `measurable_realize_symm`.

## Connection to P2, without Fubini

For every `x`, the section of a tuple carrier is measurable for the degree-`n` space, and
its degree-`n` power measure is the content of the internal section. The hypotheses
distinguish the two degrees:

| Result | Additional explicit hypotheses |
| --- | --- |
| section construction, carrier identity | none |
| section content, `sectionContentMap`, its bound, the lift bridge | none |
| measurability of each internal section | right-power nonemptiness `hXn` |
| measurability of the section-content function | left-power nonemptiness `hXm` |
| equality with the fiber's power measure | `hXn` and `hU` |

Combined-power nonemptiness is imposed nowhere; P5 takes it when it needs the degree-`m + n`
measure. Stage structure is ambient where the table says a result needs content or a measure.

## Not here

No integral identity, no section theorem for arbitrary Loeb-measurable sets, no claim that
inserting a fixed tuple is measurable for the completed spaces, and no product-σ-algebra
equivalence.
-/

namespace Loeb

open Filter MeasureTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} {U : Ultrafilter ι} {m n : ℕ}

namespace Graded

/-! ### The stagewise split under realization -/

/-- **The stagewise split, assembled**: the canonical split applied stage by stage to a pair
of elements of the ultraproducts of powers. -/
noncomputable def splitMap (a : Ultraproduct U fun i ↦ Fin m → X i)
    (b : Ultraproduct U fun i ↦ Fin n → X i) : Ultraproduct U fun i ↦ Fin (m + n) → X i :=
  Filter.Product.map₂ (fun i (a : Fin m → X i) (b : Fin n → X i) ↦ splitEquiv (X i) m n (a, b))
    a b

@[simp]
theorem splitMap_ofFun (a : (i : ι) → Fin m → X i) (b : (i : ι) → Fin n → X i) :
    splitMap (U := U) (Filter.Product.ofFun a) (Filter.Product.ofFun b)
      = Filter.Product.ofFun fun i ↦ splitEquiv (X i) m n (a i, b i) :=
  rfl

/-- **The realization commutes with the split.** Proved coordinatewise through M1's
`eval` API and the split's coordinate rules, by cases on whether the combined coordinate
lies in the left or the right block. -/
theorem realize_splitMap (a : Ultraproduct U fun i ↦ Fin m → X i)
    (b : Ultraproduct U fun i ↦ Fin n → X i) :
    realize (m + n) (splitMap a b)
      = splitEquiv (Ultraproduct U X) m n (realize m a, realize n b) := by
  funext j
  induction a, b using Filter.Product.inductionOn₂ with
  | _ a' b' => refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j <;> simp

/-- The inverse form: a split tuple, pulled back to the ultraproduct of powers, is the
stagewise split of the pulled-back blocks. This is the bridge the section proofs use. -/
theorem realize_symm_splitEquiv (x : Fin m → Ultraproduct U X) (y : Fin n → Ultraproduct U X) :
    (realize (U := U) (m + n)).symm (splitEquiv (Ultraproduct U X) m n (x, y))
      = splitMap ((realize m).symm x) ((realize n).symm y) := by
  rw [Equiv.symm_apply_eq, realize_splitMap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Graded

namespace InternalRelation

/-! ### Sections -/

/-- **The section of an internal relation at a tuple**: an internal relation of arity `n`,
obtained by assembling `x` on the stagewise side and taking stagewise sections. No
representative is chosen. -/
noncomputable def sectionAt (R : InternalRelation U X (m + n)) (x : Fin m → Ultraproduct U X) :
    InternalRelation U X n :=
  Filter.Product.map₂
    (fun i (a : Fin m → X i) (S : Set (Fin (m + n) → X i)) ↦ {b | splitEquiv (X i) m n (a, b) ∈ S})
    ((Graded.realize m).symm x) R

/-- **The representative computation rule**: a represented relation and a represented left
tuple give the represented stagewise sections. -/
@[simp]
theorem sectionAt_ofFun (S : (i : ι) → Set (Fin (m + n) → X i)) (a : (i : ι) → Fin m → X i) :
    sectionAt (Filter.Product.ofFun S : InternalRelation U X (m + n))
        (Graded.realize m (Filter.Product.ofFun a))
      = Filter.Product.ofFun fun i ↦ {b | splitEquiv (X i) m n (a i, b) ∈ S i} := by
  rw [sectionAt, Equiv.symm_apply_apply, Filter.Product.map₂_ofFun]

/-- **Exact internality of sections**: the realized section is the algebraic section of the
realized relation. Needs no stage structure. -/
theorem tupleCarrier_sectionAt (R : InternalRelation U X (m + n)) (x : Fin m → Ultraproduct U X) :
    tupleCarrier (R.sectionAt x) = Graded.sectionAt (tupleCarrier R) x := by
  ext y
  obtain ⟨a, rfl⟩ := (Graded.realize (U := U) (X := X) m).surjective x
  obtain ⟨b, rfl⟩ := (Graded.realize (U := U) (X := X) n).surjective y
  rw [mem_tupleCarrier, Graded.mem_sectionAt, mem_tupleCarrier, Graded.realize_symm_splitEquiv,
    sectionAt]
  simp only [Equiv.symm_apply_apply]
  induction a, b, R using Filter.Product.inductionOn₃ with
  | _ a' b' S => exact Iff.rfl

/-! ### Section content -/

section Content

variable [∀ i, MeasurableSpace (X i)]

/-- **The section content**: the internal content of the section at `x`, as an
`ℝ≥0∞`-valued function of the left tuple. This is the function P5 integrates. -/
noncomputable def sectionContent (R : InternalRelation U X (m + n)) (x : Fin m → Ultraproduct U X) :
    ℝ≥0∞ :=
  internalContent U (R.sectionAt x)

@[simp]
theorem sectionContent_apply (R : InternalRelation U X (m + n)) (x : Fin m → Ultraproduct U X) :
    R.sectionContent x = internalContent U (R.sectionAt x) :=
  rfl

/-- **The real-valued section-content map on the stagewise `m`-powers**: at stage `i`, the
map sending a left tuple `a` to the normalized count of its stagewise section, as a real.
Built by `Filter.Product.map` on `R`, so no representative is chosen. -/
noncomputable def sectionContentMap (R : InternalRelation U X (m + n)) :
    InternalMap U (fun i ↦ Fin m → X i) fun _ ↦ ℝ :=
  Filter.Product.map
    (fun i (S : Set (Fin (m + n) → X i)) (a : Fin m → X i) ↦
      (normalizedCounting (Fin n → X i) {b | splitEquiv (X i) m n (a, b) ∈ S}).toReal)
    R

@[simp]
theorem sectionContentMap_ofFun (S : (i : ι) → Set (Fin (m + n) → X i)) :
    sectionContentMap (Filter.Product.ofFun S : InternalRelation U X (m + n))
      = Filter.Product.ofFun fun i (a : Fin m → X i) ↦
          (normalizedCounting (Fin n → X i) {b | splitEquiv (X i) m n (a, b) ∈ S i}).toReal :=
  rfl

/-- **Uniformly bounded by `1`**, since every stagewise value is a probability. Needs only
stage measurability: `normalizedCounting_le_one` needs neither finiteness nor
nonemptiness. -/
theorem isUniformlyBounded_sectionContentMap (R : InternalRelation U X (m + n)) :
    (sectionContentMap R).IsUniformlyBounded := by
  induction R using Filter.Product.inductionOn with
  | _ S =>
    rw [sectionContentMap_ofFun, InternalMap.isUniformlyBounded_ofFun]
    refine ⟨1, Eventually.of_forall fun i a ↦ ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top (normalizedCounting_le_one _)).trans_eq
      ENNReal.toReal_one

/-- **The lift bridge**: the lift of the section-content map at the pulled-back tuple is the
real section content. Exact, for every `x`; the `toReal`/ultralimit exchange is L2's
`ultralimit_toReal`. -/
theorem lift_sectionContentMap (R : InternalRelation U X (m + n)) (x : Fin m → Ultraproduct U X) :
    InternalMap.lift (sectionContentMap R) ((Graded.realize m).symm x)
      = (R.sectionContent x).toReal := by
  obtain ⟨a, rfl⟩ := (Graded.realize (U := U) (X := X) m).surjective x
  rw [Equiv.symm_apply_apply, sectionContent_apply]
  induction a, R using Filter.Product.inductionOn₂ with
  | _ a' S =>
    rw [sectionContentMap_ofFun, InternalMap.lift_ofFun, sectionAt_ofFun, internalContent_ofFun]
    exact ultralimit_toReal (Eventually.of_forall fun i ↦ normalizedCounting_le_one _)

variable [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- **The section-content function is measurable** for the degree-`m` Loeb space. It is
`ENNReal.ofReal` of the lift of a uniformly bounded internal map, composed with the inverse
realization; M5's `measurable_lift` supplies the measurability of the lift. Takes
**left**-power nonemptiness and no `hU`. -/
theorem measurable_sectionContent (hXm : ∀ i, Nonempty (Fin m → X i))
    (R : InternalRelation U X (m + n)) :
    Measurable[Graded.powerMeasurableSpace m hXm] R.sectionContent := by
  letI := Graded.powerMeasurableSpace (U := U) m hXm
  have h : R.sectionContent = fun x ↦
      ENNReal.ofReal (InternalMap.lift (sectionContentMap R) ((Graded.realize m).symm x)) := by
    funext x
    rw [lift_sectionContentMap, sectionContent_apply,
      ENNReal.ofReal_toReal (internalContent_ne_top _)]
  rw [h]
  exact ENNReal.measurable_ofReal.comp
    ((InternalMap.measurable_lift hXm (isUniformlyBounded_sectionContentMap R)).comp
      (Graded.measurable_realize_symm m hXm))

end Content

end InternalRelation

namespace Graded

/-! ### Sections of tuple carriers and the degree-`n` measure -/

variable [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- **Every section of a tuple carrier is measurable** for the degree-`n` space: it is the
tuple carrier of the internal section. Takes right-power nonemptiness only. -/
theorem measurableSet_sectionAt_tupleCarrier (hXn : ∀ i, Nonempty (Fin n → X i))
    (R : InternalRelation U X (m + n)) (x : Fin m → Ultraproduct U X) :
    MeasurableSet[powerMeasurableSpace n hXn] (sectionAt (InternalRelation.tupleCarrier R) x) := by
  rw [← InternalRelation.tupleCarrier_sectionAt]
  exact measurableSet_tupleCarrier n hXn _

/-- **The fiber's power measure is the content of the internal section**, for every `x`.
Composes the carrier identity with P2's evaluation rule. -/
theorem powerMeasure_sectionAt_tupleCarrier (hU : (U : Filter ι).IsCountablyIncomplete)
    (hXn : ∀ i, Nonempty (Fin n → X i)) (R : InternalRelation U X (m + n))
    (x : Fin m → Ultraproduct U X) :
    powerMeasure n hU hXn (sectionAt (InternalRelation.tupleCarrier R) x)
      = internalContent U (R.sectionAt x) := by
  rw [← InternalRelation.tupleCarrier_sectionAt, powerMeasure_tupleCarrier]

end Graded

/-! ### API tests

Degree spaces are explicit in every statement. -/

section Tests

open InternalRelation

/-- **The carrier identity at an asymmetric `1 + 2` split**, and membership through it. -/
example (R : InternalRelation U X (1 + 2)) (x : Fin 1 → Ultraproduct U X)
    (y : Fin 2 → Ultraproduct U X) :
    tupleCarrier (R.sectionAt x) = Graded.sectionAt (tupleCarrier R) x
      ∧ (y ∈ tupleCarrier (R.sectionAt x) ↔ splitEquiv _ 1 2 (x, y) ∈ tupleCarrier R) :=
  ⟨tupleCarrier_sectionAt R x, by rw [tupleCarrier_sectionAt]; exact Iff.rfl⟩

/-- **Representative computation**, for a represented relation and a represented left tuple
in both shapes: through the realization, and coordinatewise. -/
example (S : (i : ι) → Set (Fin (m + n) → X i)) (a : (i : ι) → Fin m → X i) :
    sectionAt (Filter.Product.ofFun S : InternalRelation U X (m + n))
        (Graded.realize m (Filter.Product.ofFun a))
      = Filter.Product.ofFun fun i ↦ {b | splitEquiv (X i) m n (a i, b) ∈ S i} := by
  simp

example (S : (i : ι) → Set (Fin (m + n) → X i)) (a : (i : ι) → Fin m → X i) :
    sectionAt (Filter.Product.ofFun S : InternalRelation U X (m + n))
        (fun j ↦ (Filter.Product.ofFun fun i ↦ a i j : Ultraproduct U X))
      = Filter.Product.ofFun fun i ↦ {b | splitEquiv (X i) m n (a i, b) ∈ S i} := by
  simp [sectionAt]

/-- The realization/split bridge, in the direction the section proofs use. -/
example (x : Fin m → Ultraproduct U X) (y : Fin n → Ultraproduct U X) :
    (Graded.realize (U := U) (m + n)).symm (splitEquiv (Ultraproduct U X) m n (x, y))
      = Graded.splitMap ((Graded.realize m).symm x) ((Graded.realize n).symm y) :=
  Graded.realize_symm_splitEquiv x y

section StageMeasurable

variable [∀ i, MeasurableSpace (X i)]

/-- **The bound and the lift bridge need only stage measurability**: no finiteness,
discreteness, nonemptiness, or `hU` is in scope here. -/
example (R : InternalRelation U X (m + n)) (x : Fin m → Ultraproduct U X) :
    (sectionContentMap R).IsUniformlyBounded
      ∧ InternalMap.lift (sectionContentMap R) ((Graded.realize m).symm x)
          = (R.sectionContent x).toReal :=
  ⟨isUniformlyBounded_sectionContentMap R, lift_sectionContentMap R x⟩

/-- The section-content map computes on representatives. -/
example (S : (i : ι) → Set (Fin (m + n) → X i)) :
    sectionContentMap (Filter.Product.ofFun S : InternalRelation U X (m + n))
      = Filter.Product.ofFun fun i (a : Fin m → X i) ↦
          (normalizedCounting (Fin n → X i) {b | splitEquiv (X i) m n (a, b) ∈ S i}).toReal := by
  simp

end StageMeasurable

variable [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- **Measurability with no `hU` in scope**: the section-content function for the left
degree, and each internal section for the right degree. The two nonemptiness hypotheses are
about different powers. -/
example (hXm : ∀ i, Nonempty (Fin m → X i)) (hXn : ∀ i, Nonempty (Fin n → X i))
    (R : InternalRelation U X (m + n)) (x : Fin m → Ultraproduct U X) :
    Measurable[Graded.powerMeasurableSpace m hXm] R.sectionContent
      ∧ MeasurableSet[Graded.powerMeasurableSpace n hXn]
          (Graded.sectionAt (tupleCarrier R) x) :=
  ⟨measurable_sectionContent hXm R, Graded.measurableSet_sectionAt_tupleCarrier hXn R x⟩

/-- **The fiber's power measure is the section content**, at the `1 + 2` split. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX2 : ∀ i, Nonempty (Fin 2 → X i))
    (R : InternalRelation U X (1 + 2)) (x : Fin 1 → Ultraproduct U X) :
    Graded.powerMeasure 2 hU hX2 (Graded.sectionAt (tupleCarrier R) x) = R.sectionContent x :=
  Graded.powerMeasure_sectionAt_tupleCarrier hU hX2 R x

/-- **Degree zero on the right**: sections of arity `0`, whose power is nonempty over any
stages, so no stage nonemptiness is needed. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (R : InternalRelation U X (m + 0))
    (x : Fin m → Ultraproduct U X) :
    Graded.powerMeasure 0 hU (fun _ ↦ ⟨fun a ↦ a.elim0⟩) (Graded.sectionAt (tupleCarrier R) x)
      = internalContent U (R.sectionAt x) :=
  Graded.powerMeasure_sectionAt_tupleCarrier hU _ R x

/-- **Degree zero on the left**: the section-content function on the one-point degree-zero
power is measurable, again with no stage nonemptiness. -/
example (R : InternalRelation U X (0 + n)) :
    Measurable[Graded.powerMeasurableSpace 0 fun _ ↦ ⟨fun a ↦ a.elim0⟩] R.sectionContent :=
  measurable_sectionContent _ R

/-- **`0 + 0` over `Empty` stages**: both boundaries at once, where the stages themselves
carry no Loeb measure. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    (R : InternalRelation U (fun _ ↦ Empty) (0 + 0)) (x : Fin 0 → Ultraproduct U fun _ ↦ Empty) :
    Graded.powerMeasure 0 hU (fun _ ↦ ⟨fun a ↦ a.elim0⟩) (Graded.sectionAt (tupleCarrier R) x)
        = R.sectionContent x
      ∧ Measurable[Graded.powerMeasurableSpace 0 fun _ ↦ ⟨fun a ↦ a.elim0⟩] R.sectionContent :=
  ⟨Graded.powerMeasure_sectionAt_tupleCarrier hU _ R x, measurable_sectionContent _ R⟩

/-- **A genuinely dependent stage family**, at the `1 + 2` split. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    (R : InternalRelation U (fun i ↦ Fin (i + 1)) (1 + 2))
    (x : Fin 1 → Ultraproduct U fun i ↦ Fin (i + 1)) :
    Graded.powerMeasureOfNonempty 2 hU (fun _ ↦ inferInstance)
        (Graded.sectionAt (tupleCarrier R) x)
      = R.sectionContent x :=
  Graded.powerMeasure_sectionAt_tupleCarrier hU _ R x

end Tests

end Loeb
