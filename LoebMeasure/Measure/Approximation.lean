/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Measure.Envelope
import LoebMeasure.Measure.Loeb

/-!
# Internal outer approximation

The Loeb measure of an **arbitrary** set is the infimum of the contents of the internal
sets containing it:

```
loebMeasure hU hX s = ⨅ (A : InternalSet U X) (_ : s ⊆ A.carrier), internalContent U A
```

No measurability hypothesis on `s`. That is not an oversight: the Loeb measure agrees
with the induced outer measure on every set, measurable or not, because
`AddContent.measureCaratheodory` cuts down only the σ-algebra and leaves the values
alone. The approximation is therefore a statement about the outer measure wearing the
measure's name.

## Why the infimum ranges over single sets

Mathlib does prove exactly this shape generically:
`MeasureTheory.inducedOuterMeasure_eq_iInf` gives the infimum over single supersets from
the family. It is unavailable here because of its hypothesis `PU`, that the family be
closed under **countable unions**. I3 gives internal carriers only a *ring* — closed
under finite unions — and they need not be closed under countable ones, so `PU` is not
available in general. It can hold in degenerate cases: if every stage is a singleton
there are only two internal sets, and the family is trivially closed. The construction
here must work without it.

What the definition supplies unconditionally is the weaker representation as an infimum
over countable *covers*, via `MeasureTheory.OuterMeasure.ofFunction_eq_iInf_mem`, and
that is the door used below.

C7a is the Loeb-specific stand-in for the missing closure: a countable internal cover
need not have an internal union, but it does have an internal **envelope**, whose content
is the supremum of the contents of the finite partial unions and hence at most the
cover's `tsum`. That is enough to get from the cover representation to the single-set
one. This module is where C7a is spent, in `loebMeasure_eq_iInf_internal`'s hard
direction and nowhere else — the easy direction is monotonicity of the measure.

The raw `MeasureTheory.extend` and cover machinery is confined to the private lemmas
below and never reaches the public API. Downstream code sees internal sets and contents.

## Scope

The outer-approximation characterization and its ε-form. Symmetric differences, internal
representatives modulo null, and `loebMeasurable_iff_internal_mod_null` are C8.

Their difficulty is uneven, and it is worth being precise about which part is real work.
For a *measurable* `s` the ε symmetric-difference statement is a short corollary of what
is here: `exists_internal_superset_content_lt` gives an internal `A ⊇ s` with
`loebMeasure A.carrier < loebMeasure s + ε`, mathlib's
`MeasureTheory.measure_sdiff_lt_of_lt_add` turns that into
`loebMeasure (A.carrier \ s) < ε`, and `symmDiff_of_le` identifies `s ∆ A.carrier` with
`A.carrier \ s`. It is the *exact* internal-mod-null characterization — in particular
its reverse implication, which uses completeness — that is substantive.
-/

namespace Loeb

open Filter MeasureTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] {U : Ultrafilter ι}

/-! ### The cover representation

Private throughout: these expose mathlib's `extend`-and-countable-cover presentation of
the induced outer measure, which the public statements exist to hide. -/

/-- The Loeb outer measure as an infimum over countable covers by realized internal sets.
This is `OuterMeasure.ofFunction_eq_iInf_mem` with the membership predicate carried
along, so that the values are contents rather than `extend`ed contents. -/
private theorem loebOuterMeasure_eq_iInf_cover (hX : ∀ i, Nonempty (X i))
    (s : Set (Ultraproduct U X)) :
    loebOuterMeasure hX s =
      ⨅ (t : ℕ → Set (Ultraproduct U X)) (_ : ∀ i, t i ∈ InternalSet.carriers U X)
        (_ : s ⊆ ⋃ i, t i), ∑' i, internalAddContent hX (t i) := by
  rw [loebOuterMeasure, inducedOuterMeasure,
    OuterMeasure.ofFunction_eq_iInf_mem _ _ (P := fun u ↦ u ∈ InternalSet.carriers U X)
      (fun _ hu ↦ extend_eq_top _ hu) s]
  refine iInf_congr fun t ↦ iInf_congr fun ht ↦ iInf_congr fun _ ↦ ?_
  exact tsum_congr fun i ↦ extend_eq _ (ht i)

omit [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
/-- Finite subadditivity along the partial unions, in the `Finset` form the `tsum`
comparison needs.

Inherits `internalContent_sup_le`'s hypotheses, which is to say none beyond
measurability: subadditivity is an inequality and needs no stagewise measurable sets,
unlike the additivity in C3. -/
private theorem internalContent_partialSups_le_sum (A : ℕ → InternalSet U X) (n : ℕ) :
    internalContent U (partialSups A n) ≤ ∑ i ∈ Finset.range (n + 1), internalContent U (A i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : partialSups A (n + 1) = partialSups A n ⊔ A (n + 1) := by
      simpa using partialSups_succ A n
    rw [hstep, Finset.sum_range_succ]
    exact (internalContent_sup_le _ _).trans (by gcongr)

/-! ### The approximation -/

/-- **The Loeb measure is an infimum over single internal supersets.**

Valid for every `s`, with **no measurability hypothesis**: the Loeb measure is the
induced outer measure on every set.

The `≤` direction is monotonicity together with `loebMeasure_internal`. The `≥`
direction is where C7a is consumed: a countable internal cover of `s` is replaced by its
internal envelope, whose content is the supremum of the contents of the finite partial
unions and hence at most the cover's `tsum` by finite subadditivity. -/
theorem loebMeasure_eq_iInf_internal (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (s : Set (Ultraproduct U X)) :
    loebMeasure hU hX s =
      ⨅ (A : InternalSet U X) (_ : s ⊆ InternalSet.carrier A), internalContent U A := by
  refine le_antisymm (le_iInf fun A ↦ le_iInf fun hA ↦ ?_) ?_
  · rw [← loebMeasure_internal hU hX A]
    exact measure_mono hA
  · rw [loebMeasure_eq_loebOuterMeasure, loebOuterMeasure_eq_iInf_cover]
    refine le_iInf fun t ↦ le_iInf fun ht ↦ le_iInf fun hsub ↦ ?_
    -- Name an internal set behind each member of the cover, then take C7a's envelope.
    choose A hA using fun i ↦ (InternalSet.mem_carriers).1 (ht i)
    obtain ⟨B, hle, hval⟩ := exists_internal_envelope hU A
    refine iInf_le_of_le B (iInf_le_of_le ?_ ?_)
    · exact hsub.trans (Set.iUnion_subset fun i ↦ (hA i) ▸ InternalSet.carrier_mono (hle i))
    · rw [hval]
      refine iSup_le fun n ↦ (internalContent_partialSups_le_sum A n).trans ?_
      refine (Finset.sum_le_sum fun i _ ↦ ?_).trans (ENNReal.sum_le_tsum _)
      exact le_of_eq (by rw [← hA i, internalAddContent_carrier])

/-- **Outer approximation within `ε`**, for an arbitrary set.

Again no measurability hypothesis. The strictness comes from the Loeb measure being
finite — it is a probability measure — so that `loebMeasure hU hX s < loebMeasure hU hX s
+ ε` and the infimum above is not attained vacuously. -/
theorem exists_internal_superset_content_lt (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (s : Set (Ultraproduct U X)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : InternalSet U X, s ⊆ InternalSet.carrier A ∧
      internalContent U A < loebMeasure hU hX s + ε := by
  have hlt : (⨅ (A : InternalSet U X) (_ : s ⊆ InternalSet.carrier A), internalContent U A)
      < loebMeasure hU hX s + ε := by
    rw [← loebMeasure_eq_iInf_internal hU hX]
    exact ENNReal.lt_add_right (measure_ne_top _ _) hε.ne'
  simpa only [iInf_lt_iff, exists_prop] using hlt

/-! ### API tests -/

section Tests

variable (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))

/-- **Approximation of an arbitrary set**, with no measurability hypothesis anywhere in
the statement. This is the shape C8 consumes. -/
example (s : Set (Ultraproduct U X)) :
    ∃ A : InternalSet U X, s ⊆ InternalSet.carrier A ∧
      internalContent U A < loebMeasure hU hX s + 1 :=
  exists_internal_superset_content_lt hU hX s one_pos

/-- The characterization is consistent with the defining property: an internal set
approximates itself exactly. -/
example (A : InternalSet U X) :
    loebMeasure hU hX (InternalSet.carrier A) ≤ internalContent U A :=
  le_of_eq (loebMeasure_internal hU hX A)

/-- **Every set has some internal superset of content within `ε`** — instantiated at a
genuinely dependent family of stages. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    (s : Set (Ultraproduct U fun i ↦ Fin (i + 1))) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : InternalSet U fun i ↦ Fin (i + 1), s ⊆ InternalSet.carrier A ∧
      internalContent U A < loebMeasure hU (fun _ ↦ ⟨0⟩) s + ε :=
  exists_internal_superset_content_lt hU _ s hε

/-- The infimum form, on an arbitrary set. -/
example (s : Set (Ultraproduct U X)) :
    loebMeasure hU hX s
      = ⨅ (A : InternalSet U X) (_ : s ⊆ InternalSet.carrier A), internalContent U A :=
  loebMeasure_eq_iInf_internal hU hX s

/-- The measure and the outer measure agree off the σ-algebra too — the bridge is
pointwise on all of `Set`. -/
example (s : Set (Ultraproduct U X)) : loebMeasure hU hX s = loebOuterMeasure hX s :=
  loebMeasure_eq_loebOuterMeasure hU hX s

end Tests

end Loeb
