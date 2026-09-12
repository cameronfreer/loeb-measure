/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.Relation
import LoebMeasure.Measure.Loeb

/-!
# Loeb structures on realized finite powers

The Loeb σ-algebra and Loeb measure of the ultraproduct of `n`-th stage powers,
transported along the realization

```
e_n : Ultraproduct U (fun i ↦ Fin n → X i) ≃ (Fin n → Ultraproduct U X)
```

which is the existing `Filter.Product.finPowerEquiv`. Nothing is constructed twice: the
degree-`n` space is `loebMeasurableSpace` on the ultraproduct of powers, pushed along
`e_n`, and the degree-`n` measure is `loebMeasure` there, pushed along the resulting
measurable equivalence. This is the concrete construction that ADR-0005's bundle will later
package; the bundle itself does not appear here.

## Not the product σ-algebra

`powerMeasurableSpace n` is the **full Loeb σ-algebra** on the realized power. It is not
`MeasurableSpace.pi`, and in general it is strictly larger. No instance is registered on
`Fin n → Ultraproduct U X`, precisely so that nothing can pick up the product σ-algebra by
accident; every use binds the degree's space explicitly, as `loebMeasurableSpace` already
requires.

## Hypotheses

M3's split, preserved degree by degree:

* the transported σ-algebra, the measurable equivalence, and measurability of tuple
  carriers take **nonemptiness of the stage powers** `∀ i, Nonempty (Fin n → X i)` and
  nothing else explicit;
* the measure, its probability and completeness, and the content evaluation additionally
  take `hU`.

Nonemptiness is taken on the powers rather than on the stages: `Fin 0 → X i` is nonempty
whatever `X i` is, so **degree zero is available over empty stages**, and a test says so.
Convenience forms derive power nonemptiness from ordinary `hX` for positive degrees and
any degree alike. The finite discrete stage structure remains ambient.

## The transport rule needs no measurability

`powerMeasure_apply` holds for **every** set, measurable or not, because
`MeasurableEquiv.map_apply` does. That is what makes the rule usable on sets that are
measurable only by completeness.

## Scope

Realization as tuples, and the internal-relation interface: a tuple carrier is measurable
and its power measure is the content. Permutation measure preservation, cross-degree
projections and the canonical split are later units; the U5 identities describing how
reindexing commutes with realization are consumed there, not restated here.
-/

namespace Loeb

open MeasureTheory

variable {ι : Type*} {X : ι → Type*} {U : Ultrafilter ι}

/-- Nonemptiness of every stage gives nonemptiness of every stage power, at every degree.
The converse fails at degree zero, which is the point of taking power nonemptiness in the
graded constructions. -/
theorem nonempty_fin_pi (hX : ∀ i, Nonempty (X i)) (n : ℕ) (i : ι) :
    Nonempty (Fin n → X i) :=
  ⟨fun _ ↦ (hX i).some⟩

namespace Graded

variable [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- **The realization of the degree-`n` power as tuples**: `Filter.Product.finPowerEquiv`,
under a short local name. -/
noncomputable abbrev realize (n : ℕ) :
    Ultraproduct U (fun i ↦ Fin n → X i) ≃ (Fin n → Ultraproduct U X) :=
  Filter.Product.finPowerEquiv (l := (U : Filter ι)) (X := X) n

/-! ### The σ-algebra and the measurable equivalence -/

/-- **The degree-`n` Loeb σ-algebra on the realized power**: the full Loeb σ-algebra of
the ultraproduct of `n`-th stage powers, transported along `realize n`.

`@[reducible]` for the same reason as `loebMeasurableSpace`: the class-type linter
requires it, so that `MeasurableSet` under this space unfolds where needed. Takes only
nonemptiness of the stage powers. -/
@[reducible]
noncomputable def powerMeasurableSpace (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i)) :
    MeasurableSpace (Fin n → Ultraproduct U X) :=
  (loebMeasurableSpace hXn).map (realize n)

/-- **The realization as a measurable equivalence**, from the Loeb space on the
ultraproduct of powers to the transported space on tuples. Forward measurability is
definitional for `MeasurableSpace.map`; inverse measurability is that `e ⁻¹' (e.symm ⁻¹' s)`
is `s`. -/
noncomputable def realizeEquiv (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i)) :
    @MeasurableEquiv (Ultraproduct U fun i ↦ Fin n → X i) (Fin n → Ultraproduct U X)
      (loebMeasurableSpace hXn) (powerMeasurableSpace n hXn) :=
  letI := loebMeasurableSpace (U := U) hXn
  letI := powerMeasurableSpace (U := U) n hXn
  { toEquiv := realize n
    measurable_toFun := fun _ hs ↦ hs
    measurable_invFun := fun s hs ↦ by
      change MeasurableSet[loebMeasurableSpace hXn] (realize n ⁻¹' ((realize n).symm ⁻¹' s))
      rwa [Equiv.preimage_symm_preimage] }

@[simp]
theorem realizeEquiv_apply (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i))
    (x : Ultraproduct U fun i ↦ Fin n → X i) :
    realizeEquiv n hXn x = realize n x :=
  rfl

@[simp]
theorem realizeEquiv_symm_apply (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i))
    (x : Fin n → Ultraproduct U X) :
    @MeasurableEquiv.symm _ _ (loebMeasurableSpace hXn) (powerMeasurableSpace n hXn)
      (realizeEquiv n hXn) x = (realize n).symm x :=
  rfl

/-- The realization is measurable, from the Loeb space to the transported space. -/
theorem measurable_realize (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i)) :
    @Measurable (Ultraproduct U fun i ↦ Fin n → X i) (Fin n → Ultraproduct U X)
      (loebMeasurableSpace hXn) (powerMeasurableSpace n hXn) (realize n) :=
  letI := loebMeasurableSpace (U := U) hXn
  letI := powerMeasurableSpace (U := U) n hXn
  (realizeEquiv n hXn).measurable

/-- And its inverse is measurable the other way. -/
theorem measurable_realize_symm (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i)) :
    @Measurable (Fin n → Ultraproduct U X) (Ultraproduct U fun i ↦ Fin n → X i)
      (powerMeasurableSpace n hXn) (loebMeasurableSpace hXn) (realize n).symm :=
  letI := loebMeasurableSpace (U := U) hXn
  letI := powerMeasurableSpace (U := U) n hXn
  (realizeEquiv n hXn).symm.measurable

/-- **A tuple carrier is measurable** for the degree-`n` space: it is the preimage of a
realized internal set under the inverse realization. Takes only power nonemptiness. -/
theorem measurableSet_tupleCarrier (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i))
    (R : InternalRelation U X n) :
    @MeasurableSet _ (powerMeasurableSpace n hXn) (InternalRelation.tupleCarrier R) :=
  letI := loebMeasurableSpace (U := U) hXn
  letI := powerMeasurableSpace (U := U) n hXn
  (realizeEquiv n hXn).symm.measurable (measurableSet_internal hXn R)

/-! ### The measure -/

/-- **The degree-`n` Loeb measure on the realized power**: `loebMeasure` on the
ultraproduct of powers, pushed forward along the realization. `hU` enters here and not
before. -/
noncomputable def powerMeasure (n : ℕ) (hU : (U : Filter ι).IsCountablyIncomplete)
    (hXn : ∀ i, Nonempty (Fin n → X i)) :
    @Measure (Fin n → Ultraproduct U X) (powerMeasurableSpace n hXn) :=
  letI := loebMeasurableSpace (U := U) hXn
  letI := powerMeasurableSpace (U := U) n hXn
  (loebMeasure hU hXn).map (realizeEquiv n hXn)

/-- **The transport rule, for every set.** No measurability hypothesis on `s`:
`MeasurableEquiv.map_apply` needs none, and that is what makes this rule usable on sets
that are measurable only by completeness. -/
theorem powerMeasure_apply (n : ℕ) (hU : (U : Filter ι).IsCountablyIncomplete)
    (hXn : ∀ i, Nonempty (Fin n → X i)) (s : Set (Fin n → Ultraproduct U X)) :
    powerMeasure n hU hXn s = loebMeasure hU hXn (realize n ⁻¹' s) :=
  letI := loebMeasurableSpace (U := U) hXn
  letI := powerMeasurableSpace (U := U) n hXn
  (realizeEquiv n hXn).map_apply (μ := loebMeasure hU hXn) s

/-- **The degree-`n` measure is a probability measure.** -/
instance isProbabilityMeasure_powerMeasure (n : ℕ) (hU : (U : Filter ι).IsCountablyIncomplete)
    (hXn : ∀ i, Nonempty (Fin n → X i)) :
    @IsProbabilityMeasure _ (powerMeasurableSpace n hXn) (powerMeasure n hU hXn) :=
  letI := loebMeasurableSpace (U := U) hXn
  letI := powerMeasurableSpace (U := U) n hXn
  Measure.isProbabilityMeasure_map (realizeEquiv n hXn).measurable.aemeasurable

/-- **The degree-`n` measure is complete.** Proved directly: a null set pulls back to a
Loeb-null set, which is measurable by `isComplete_loebMeasure`, and pushes forward again
along the inverse realization. Mathlib has no lemma transporting completeness along a
measurable equivalence, so this is the argument rather than an appeal. -/
instance isComplete_powerMeasure (n : ℕ) (hU : (U : Filter ι).IsCountablyIncomplete)
    (hXn : ∀ i, Nonempty (Fin n → X i)) :
    @Measure.IsComplete _ (powerMeasurableSpace n hXn) (powerMeasure n hU hXn) := by
  letI := loebMeasurableSpace (U := U) hXn
  letI := powerMeasurableSpace (U := U) n hXn
  refine ⟨fun s hs ↦ ?_⟩
  rw [powerMeasure_apply] at hs
  have hm := (isComplete_loebMeasure hU hXn).out _ hs
  have : s = (realize n).symm ⁻¹' (realize n ⁻¹' s) := by
    ext x
    change x ∈ s ↔ realize n ((realize n).symm x) ∈ s
    rw [Equiv.apply_symm_apply]
  rw [this]
  exact (realizeEquiv n hXn).symm.measurable hm

/-- **The internal-relation interface**: the power measure of a tuple carrier is the
internal content of the relation. Composes the transport rule with M3's
`loebMeasure_internal`. -/
theorem powerMeasure_tupleCarrier (n : ℕ) (hU : (U : Filter ι).IsCountablyIncomplete)
    (hXn : ∀ i, Nonempty (Fin n → X i)) (R : InternalRelation U X n) :
    powerMeasure n hU hXn (InternalRelation.tupleCarrier R) = internalContent U R := by
  rw [powerMeasure_apply, ← loebMeasure_internal hU hXn]
  congr 1
  ext x
  change realize n x ∈ InternalRelation.tupleCarrier R ↔ _
  rw [InternalRelation.mem_tupleCarrier]
  change (realize n).symm (realize n x) ∈ _ ↔ _
  rw [Equiv.symm_apply_apply]

/-! ### Convenience forms from stage nonemptiness

For callers holding ordinary `hX`. These are abbreviations, so every lemma above applies
to them by unfolding. -/

/-- The degree-`n` space, from stage nonemptiness. -/
noncomputable abbrev powerMeasurableSpaceOfNonempty (n : ℕ) (hX : ∀ i, Nonempty (X i)) :
    MeasurableSpace (Fin n → Ultraproduct U X) :=
  powerMeasurableSpace n (nonempty_fin_pi hX n)

/-- The degree-`n` measure, from stage nonemptiness. -/
noncomputable abbrev powerMeasureOfNonempty (n : ℕ) (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) :
    @Measure (Fin n → Ultraproduct U X) (powerMeasurableSpaceOfNonempty n hX) :=
  powerMeasure n hU (nonempty_fin_pi hX n)

/-! ### API tests

Measurable spaces are explicit in every statement, so none can silently select the product
σ-algebra on `Fin n → Ultraproduct U X`. -/

section Tests

/-- **Degree zero over `Empty` stages.** The stages are empty, so `loebMeasure` on `X`
itself does not exist; but `Fin 0 → Empty` is a singleton, the degree-zero power is
nonempty, and the degree-zero measure is a probability measure. This is why nonemptiness is
taken on the powers. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete) :
    powerMeasure (X := fun _ ↦ Empty) 0 hU (fun _ ↦ ⟨fun a ↦ a.elim0⟩) Set.univ = 1 :=
  @measure_univ _ (powerMeasurableSpace 0 _) _ inferInstance

/-- **Degree one**, from ordinary stage nonemptiness, with the transport rule. Agreement
with `loebMeasure` on `X` itself is not claimed here: no transport of the Loeb measure
along stagewise bijections exists yet, and that belongs to coordinate compatibility. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (s : Set (Fin 1 → Ultraproduct U X)) :
    powerMeasureOfNonempty 1 hU hX s = loebMeasure hU (nonempty_fin_pi hX 1) (realize 1 ⁻¹' s) :=
  powerMeasure_apply 1 hU _ s

/-- **A genuinely dependent stage family**, at degree two. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete) :
    @IsProbabilityMeasure _
      (powerMeasurableSpaceOfNonempty (X := fun n ↦ Fin (n + 1)) 2 fun _ ↦ inferInstance)
      (powerMeasureOfNonempty 2 hU fun _ ↦ inferInstance) :=
  inferInstance

/-- **Both directions of the measurable equivalence**, as measurability statements with
their spaces explicit. -/
example (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i)) :
    @Measurable (Ultraproduct U fun i ↦ Fin n → X i) (Fin n → Ultraproduct U X)
        (loebMeasurableSpace hXn) (powerMeasurableSpace n hXn) (realize n)
      ∧ @Measurable (Fin n → Ultraproduct U X) (Ultraproduct U fun i ↦ Fin n → X i)
          (powerMeasurableSpace n hXn) (loebMeasurableSpace hXn) (realize n).symm :=
  ⟨measurable_realize n hXn, measurable_realize_symm n hXn⟩

/-- **Evaluation on a tuple carrier**: an internal relation's realized tuple set has power
measure equal to its content. -/
example (n : ℕ) (hU : (U : Filter ι).IsCountablyIncomplete) (hXn : ∀ i, Nonempty (Fin n → X i))
    (R : InternalRelation U X n) :
    powerMeasure n hU hXn (InternalRelation.tupleCarrier R) = internalContent U R :=
  powerMeasure_tupleCarrier n hU hXn R

/-- The σ-algebra results need no `hU`: this statement mentions only power nonemptiness. -/
example (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i)) (R : InternalRelation U X n) :
    @MeasurableSet _ (powerMeasurableSpace n hXn) (InternalRelation.tupleCarrier R) :=
  measurableSet_tupleCarrier n hXn R

/-- Completeness, usable as an instance under the explicit space. -/
example (n : ℕ) (hU : (U : Filter ι).IsCountablyIncomplete) (hXn : ∀ i, Nonempty (Fin n → X i))
    (s : Set (Fin n → Ultraproduct U X)) (hs : powerMeasure n hU hXn s = 0) :
    @MeasurableSet _ (powerMeasurableSpace n hXn) s :=
  (isComplete_powerMeasure n hU hXn).out s hs

end Tests

end Graded

end Loeb
