/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Measure.Envelope
import LoebMeasure.Measure.Loeb

/-!
# Internal approximation

Two results, in increasing strength. First, the Loeb measure of an **arbitrary** set is
the infimum of the contents of the internal sets containing it. Second, a **measurable**
set is an internal set modulo null — which is the working description of Loeb
measurability, and the form the applications use.

## Outer approximation

For every `s`:

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

## Measurable sets are internal modulo null

`loebMeasurable_iff_internal_mod_null`. Measurability is exactly what turns the one-sided
outer bound into a two-sided estimate: `sᶜ` is measurable too, so complementing an outer
approximation of `sᶜ` gives an *inner* approximation of `s` — internal sets are a Boolean
algebra and the Loeb measure has total mass `1`.

The difficulty is uneven across the four steps, and worth naming:

* `loebMeasure_eq_zero_iff` and `exists_internal_symmDiff_lt` are short. The latter is
  `exists_internal_superset_content_lt`, then `MeasureTheory.measure_sdiff_lt_of_lt_add`,
  then `symmDiff_of_le`;
* `exists_internal_symmDiff_eq_zero` is the real work, and where **C7a is spent a second
  time** — in the *increasing* direction, where the outer approximation spent it on
  covers. C7a's content *equality*, not merely a bound, is what pins the envelope's
  measure to `loebMeasure s`;
* the reverse implication of `loebMeasurable_iff_internal_mod_null` is the only theorem
  in the library whose proof consumes **completeness**. `Measure/Loeb.lean` exercises the
  instance in a test, but no earlier theorem needed it.

## Scope

Approximation only. Atomlessness is C9, and the graded and application layers are later
milestones.
-/

namespace Loeb

open Filter MeasureTheory
open scoped ENNReal symmDiff

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

/-! ### Nullity

The first consequence, and the cheapest: it needs neither measurability of `s` nor
anything beyond C7b. -/

/-- **A set is null exactly when internal sets of arbitrarily small content cover it.**

No measurability hypothesis, inherited from C7b. -/
theorem loebMeasure_eq_zero_iff (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (s : Set (Ultraproduct U X)) :
    loebMeasure hU hX s = 0 ↔
      ∀ ε : ℝ≥0∞, 0 < ε →
        ∃ A : InternalSet U X, s ⊆ InternalSet.carrier A ∧ internalContent U A < ε := by
  constructor
  · intro h ε hε
    obtain ⟨A, hsub, hlt⟩ := exists_internal_superset_content_lt hU hX s hε
    exact ⟨A, hsub, by rwa [h, zero_add] at hlt⟩
  · intro h
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) zero_le
    obtain ⟨A, hsub, hlt⟩ := h ε (ENNReal.coe_pos.2 hε)
    rw [zero_add]
    calc loebMeasure hU hX s
        ≤ loebMeasure hU hX (InternalSet.carrier A) := measure_mono hsub
      _ = internalContent U A := loebMeasure_internal hU hX A
      _ ≤ (ε : ℝ≥0∞) := hlt.le

/-! ### Two-sided approximation of measurable sets

From here on `s` is Loeb measurable. Measurability is what turns C7b's one-sided outer
bound into a two-sided estimate: `sᶜ` is then measurable too, and complementing an outer
approximation of `sᶜ` gives an inner approximation of `s`, because internal sets are a
Boolean algebra and the Loeb measure is a probability measure. -/

/-- **Approximation in symmetric difference, within `ε`.**

Short, and worth seeing why: the outer approximation already gives an internal `A ⊇ s`
whose measure exceeds `loebMeasure s` by less than `ε`; measurability of `s` turns that
into a bound on the *difference* `A.carrier \ s`, and since `s ⊆ A.carrier` that
difference is the symmetric difference. Only the outer half is used — the inner
approximation below is not needed here. -/
theorem exists_internal_symmDiff_lt (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) {s : Set (Ultraproduct U X)}
    (hs : MeasurableSet[loebMeasurableSpace hX] s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : InternalSet U X, s ⊆ InternalSet.carrier A ∧
      loebMeasure hU hX (s ∆ InternalSet.carrier A) < ε := by
  obtain ⟨A, hsub, hlt⟩ := exists_internal_superset_content_lt hU hX s hε
  refine ⟨A, hsub, ?_⟩
  rw [symmDiff_of_le hsub]
  refine measure_sdiff_lt_of_lt_add hs.nullMeasurableSet hsub (measure_ne_top _ _) ?_
  rwa [loebMeasure_internal hU hX A]

/-- **Inner approximation by internal sets.** The complement of C7b's outer approximation
of `sᶜ`.

Two structural facts do the work: `InternalSet.carrier_compl` — an ultrafilter result —
to see the complement of an internal set as an internal set, and total mass `1` to
convert the bound on `sᶜ` into one on `s`. Both appear more than once in the proof, since
the complement identity is needed for the containment and again inside the mass
computation. -/
theorem exists_internal_subset_lt_content_add (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) {s : Set (Ultraproduct U X)}
    (hs : MeasurableSet[loebMeasurableSpace hX] s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : InternalSet U X, InternalSet.carrier A ⊆ s ∧
      loebMeasure hU hX s < internalContent U A + ε := by
  obtain ⟨A, hsub, hlt⟩ := exists_internal_superset_content_lt hU hX sᶜ hε
  refine ⟨Aᶜ, ?_, ?_⟩
  · rw [InternalSet.carrier_compl]
    exact Set.compl_subset_comm.1 hsub
  · have hAmeas := measurableSet_internal hX A
    have hcompl : internalContent U Aᶜ + internalContent U A = 1 := by
      rw [← loebMeasure_internal hU hX, ← loebMeasure_internal hU hX,
        InternalSet.carrier_compl, ← measure_univ (μ := loebMeasure hU hX),
        ← measure_add_measure_compl (μ := loebMeasure hU hX) hAmeas, add_comm]
    have hs' : loebMeasure hU hX s + loebMeasure hU hX sᶜ = 1 := by
      rw [← measure_univ (μ := loebMeasure hU hX)]
      exact measure_add_measure_compl hs
    -- Cancel the finite `loebMeasure sᶜ` from `1 < internalContent Aᶜ + ε + loebMeasure sᶜ`.
    have hkey : loebMeasure hU hX s + loebMeasure hU hX sᶜ
        < internalContent U Aᶜ + ε + loebMeasure hU hX sᶜ := by
      rw [hs', ← hcompl, ← loebMeasure_internal hU hX A]
      calc internalContent U Aᶜ + loebMeasure hU hX (InternalSet.carrier A)
          < internalContent U Aᶜ + (loebMeasure hU hX sᶜ + ε) := by
            refine ENNReal.add_lt_add_left (internalContent_ne_top _) ?_
            rwa [loebMeasure_internal hU hX A]
        _ = internalContent U Aᶜ + ε + loebMeasure hU hX sᶜ := by ring
    exact lt_of_add_lt_add_right hkey

omit [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
/-- Carriers of the partial unions stay inside any common upper bound. Plain induction
through `InternalSet.carrier_sup`; kept private since only the representative theorem
needs it. -/
private theorem carrier_partialSups_subset {C : ℕ → InternalSet U X}
    {t : Set (Ultraproduct U X)} (h : ∀ n, InternalSet.carrier (C n) ⊆ t) (n : ℕ) :
    InternalSet.carrier (partialSups C n) ⊆ t := by
  induction n with
  | zero => simpa using h 0
  | succ n ih =>
    have hstep : partialSups C (n + 1) = partialSups C n ⊔ C (n + 1) := by
      simpa using partialSups_succ C n
    rw [hstep, InternalSet.carrier_sup]
    exact Set.union_subset ih (h (n + 1))

/-- **Every Loeb measurable set has an internal representative modulo null.**

The substantive step, and where C7a is spent a second time — in the *increasing*
direction this time, C7b having spent it on covers.

Take inner approximations `C n ⊆ s` with content within `1 / (n + 1)` of `loebMeasure s`,
and let `B` be their envelope. Their union `E` satisfies `E ⊆ s`, `E ⊆ B.carrier`, and
`loebMeasure E = loebMeasure s` — the last because each `C n` alone already forces
`loebMeasure s ≤ loebMeasure E + 1 / (n + 1)`. Meanwhile C7a's *equality* pins
`loebMeasure B.carrier` to the supremum of the partial-union contents, each of which is
at most `loebMeasure s` since those partial unions also sit inside `s`. So `E`,
`s ∩ B.carrier`, `s` and `B.carrier` all have the same measure, and both halves of the
symmetric difference are squeezed to zero. -/
theorem exists_internal_symmDiff_eq_zero (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) {s : Set (Ultraproduct U X)}
    (hs : MeasurableSet[loebMeasurableSpace hX] s) :
    ∃ A : InternalSet U X, loebMeasure hU hX (s ∆ InternalSet.carrier A) = 0 := by
  -- Inner approximations, and C7a's envelope over them.
  have hpos : ∀ n : ℕ, (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
    fun n ↦ ENNReal.inv_pos.2 (by simp [ENNReal.add_eq_top])
  choose C hCsub hClt using fun n : ℕ ↦
    exists_internal_subset_lt_content_add hU hX hs (hpos n)
  obtain ⟨B, hle, hval⟩ := exists_internal_envelope hU C
  set E : Set (Ultraproduct U X) := ⋃ n, InternalSet.carrier (C n) with hE
  have hEs : E ⊆ s := Set.iUnion_subset hCsub
  have hEB : E ⊆ InternalSet.carrier B :=
    Set.iUnion_subset fun n ↦ InternalSet.carrier_mono (hle n)
  -- `E` already has full measure: one `C n` at a time suffices.
  have hEeq : loebMeasure hU hX E = loebMeasure hU hX s := by
    refine le_antisymm (measure_mono hEs) ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
    have hstep : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (ε : ℝ≥0∞) :=
      (ENNReal.inv_le_inv.2 le_self_add).trans hn.le
    refine (hClt n).le.trans ?_
    gcongr
    rw [← loebMeasure_internal hU hX]
    exact measure_mono (Set.subset_iUnion (fun k ↦ InternalSet.carrier (C k)) n)
  -- C7a's equality pins the envelope's measure to the same value.
  have hBeq : loebMeasure hU hX (InternalSet.carrier B) = loebMeasure hU hX s := by
    refine le_antisymm ?_ (hEeq ▸ measure_mono hEB)
    rw [loebMeasure_internal, hval]
    refine iSup_le fun n ↦ ?_
    rw [← loebMeasure_internal hU hX]
    exact measure_mono (carrier_partialSups_subset hCsub n)
  -- Both halves of the symmetric difference are null.
  have hinter : loebMeasure hU hX (s ∩ InternalSet.carrier B) = loebMeasure hU hX s :=
    le_antisymm (measure_mono Set.inter_subset_left)
      (hEeq ▸ measure_mono (Set.subset_inter hEs hEB))
  have hdiff1 : loebMeasure hU hX (s \ InternalSet.carrier B) = 0 := by
    have h := measure_inter_add_sdiff (μ := loebMeasure hU hX) s (measurableSet_internal hX B)
    rw [hinter] at h
    exact (ENNReal.add_right_inj (measure_ne_top _ _)).1 (h.trans (add_zero _).symm)
  have hdiff2 : loebMeasure hU hX (InternalSet.carrier B \ s) = 0 := by
    have h := measure_inter_add_sdiff (μ := loebMeasure hU hX) (InternalSet.carrier B) hs
    rw [Set.inter_comm, hinter, hBeq] at h
    exact (ENNReal.add_right_inj (measure_ne_top _ _)).1 (h.trans (add_zero _).symm)
  refine ⟨B, le_antisymm ?_ zero_le⟩
  rw [Set.symmDiff_def]
  exact le_of_le_of_eq (measure_union_le _ _) (by rw [hdiff1, hdiff2, add_zero])

/-- **Loeb measurability is exactly internality modulo null.**

The forward direction is the representative above. The reverse is where **completeness**
is used, and it is the only place in the project that needs it: the symmetric difference
is null, hence measurable by completeness, and `s = A.carrier ∆ (s ∆ A.carrier)` is then
a symmetric difference of measurable sets. Without completeness the null set need not be
measurable and the argument would not close. -/
theorem loebMeasurable_iff_internal_mod_null (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (s : Set (Ultraproduct U X)) :
    MeasurableSet[loebMeasurableSpace hX] s ↔
      ∃ A : InternalSet U X, loebMeasure hU hX (s ∆ InternalSet.carrier A) = 0 := by
  refine ⟨fun hs ↦ exists_internal_symmDiff_eq_zero hU hX hs, ?_⟩
  rintro ⟨A, hA⟩
  have hnull : MeasurableSet[loebMeasurableSpace hX] (s ∆ InternalSet.carrier A) :=
    measurableSet_of_null hA
  have hrw : s = InternalSet.carrier A ∆ (s ∆ InternalSet.carrier A) := by
    rw [symmDiff_comm s, symmDiff_symmDiff_cancel_left]
  rw [hrw]
  exact (measurableSet_internal hX A).symmDiff hnull

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

/-- **The nullity criterion applies to an arbitrary set**, with no measurability
hypothesis. -/
example (s : Set (Ultraproduct U X)) (h : loebMeasure hU hX s = 0) (ε : ℝ≥0∞)
    (hε : 0 < ε) :
    ∃ A : InternalSet U X, s ⊆ InternalSet.carrier A ∧ internalContent U A < ε :=
  (loebMeasure_eq_zero_iff hU hX s).1 h ε hε

/-- **The headline characterization**, in the shape the blueprint specified and the
applications will use. -/
example (s : Set (Ultraproduct U X)) :
    MeasurableSet[loebMeasurableSpace hX] s ↔
      ∃ A : InternalSet U X, loebMeasure hU hX (s ∆ InternalSet.carrier A) = 0 :=
  loebMeasurable_iff_internal_mod_null hU hX s

/-- **Realized internal sets satisfy it trivially**, which is the sanity check that the
characterization is oriented correctly: take `A` to be the set itself. -/
example (A : InternalSet U X) :
    ∃ A' : InternalSet U X,
      loebMeasure hU hX (InternalSet.carrier A ∆ InternalSet.carrier A') = 0 :=
  ⟨A, by simp⟩

/-- **A null set is measurable**, from completeness and no approximation at all.

Not to be confused with the characterization: a null set is internal modulo null for the
trivial reason that `⊥` works, and that direction needs nothing. What completeness
supplies is the *measurability*, which is exactly the content of the reverse implication
of `loebMeasurable_iff_internal_mod_null`. -/
example (s : Set (Ultraproduct U X)) (h : loebMeasure hU hX s = 0) :
    MeasurableSet[loebMeasurableSpace hX] s :=
  measurableSet_of_null h

/-- The trivial direction, for contrast with the one above: a null set is internal modulo
null with `A = ⊥`, no completeness involved. -/
example (s : Set (Ultraproduct U X)) (h : loebMeasure hU hX s = 0) :
    ∃ A : InternalSet U X, loebMeasure hU hX (s ∆ InternalSet.carrier A) = 0 :=
  ⟨⊥, by rw [InternalSet.carrier_bot, ← Set.bot_eq_empty, symmDiff_bot]; exact h⟩

/-- Inner approximation, the two-sided half. Needs measurability, unlike its outer
counterpart. -/
example {s : Set (Ultraproduct U X)} (hs : MeasurableSet[loebMeasurableSpace hX] s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : InternalSet U X, InternalSet.carrier A ⊆ s ∧
      loebMeasure hU hX s < internalContent U A + ε :=
  exists_internal_subset_lt_content_add hU hX hs hε

/-- **The symmetric-difference form on a genuinely dependent family of stages.** -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    {s : Set (Ultraproduct U fun i ↦ Fin (i + 1))}
    (hs : MeasurableSet[loebMeasurableSpace (fun _ ↦ ⟨0⟩)] s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : InternalSet U fun i ↦ Fin (i + 1), s ⊆ InternalSet.carrier A ∧
      loebMeasure hU (fun _ ↦ ⟨0⟩) (s ∆ InternalSet.carrier A) < ε :=
  exists_internal_symmDiff_lt hU _ hs hε

end Tests

end Loeb
