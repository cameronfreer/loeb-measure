/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Measure.Approximation

/-!
# Points, splitting, and atomlessness

Three results, in increasing strength: the measure of a point, the fact that internal
sets halve, and atomlessness of the Loeb measure.

## Null singletons are not atomlessness

The two are genuinely different, and mathlib says so: the `NoAtoms` it plans is
`∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s`, and
its own note records that this implies `MeasureTheory.NullSingletonClass` but *not*
conversely — the countable–cocountable probability measure has every singleton null while
the whole space is an atom. So `nullSingletonClass_loebMeasure` below is not on its own
the atomlessness this milestone promised; `exists_measurableSet_subset_measure_lt` is.

## Points are cheap; splitting is not

A singleton of the ultraproduct is *already* the carrier of an internal set, since
eventual stagewise equality is equality in the ultraproduct
(`InternalSet.carrier_ofFun_singleton`). So `loebMeasure_internal` computes a point's
measure directly, with no approximation:

```
loebMeasure hU hX {x} = U.ultralimit fun i ↦ ((Nat.card (X i) : ℝ≥0∞))⁻¹
```

Atomlessness costs more. It needs an internal set to *split*, which is
`exists_internal_le_content_eq_half`: choosing stagewise subsets of half the cardinality
gives an internal `B ≤ A` of exactly half the content. "Exactly" survives the floor in
`n / 2` because the error is at most one point per stage, and one point per stage is
precisely what the growth hypothesis kills.

The measurable statement then combines this with C8: a measurable set of positive measure
agrees almost everywhere with an internal set, whose half meets it in a set of half the
measure.

## The hypothesis is real, not bookkeeping

None of this holds without growth. If every stage is a singleton the ultraproduct is one
point of measure `1` — an atom — and `loebMeasure_singleton_eq_one_of_subsingleton`
records that as a compiled statement. `StagesUnbounded U X` asks that every `n` be
eventually a lower bound on the stage cardinalities, phrased that way rather than as a
vanishing ultralimit because it is what applications can check.

Only the *sufficient* direction is proved: growth gives atomlessness. The subsingleton
theorem is one counterexample to dropping the hypothesis, not a converse, and no
equivalence is claimed anywhere here.

## Why these are theorems and not instances

`StagesUnbounded U X` does not appear in `loebMeasure hU hX`, so typeclass inference
cannot recover it — unlike `hU` and `hX`, which do appear and are carried fine. Callers
introduce the conclusion with `haveI`; the tests do exactly that.

## Scope

Points, splitting into halves, and atomlessness. The full Lyapunov statement — that the
*range* of the measure is all of `[0, 1]`, not merely that it contains a strictly
intermediate value — needs iterating the split and a limit argument, and is not attempted
here.
-/

namespace Loeb

open Filter MeasureTheory
open scoped ENNReal symmDiff

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] {U : Ultrafilter ι}

/-! ### The measure of a point -/

/-- **The measure of a point** is the ultralimit of the reciprocal stage cardinalities.

Note what is *absent*: no approximation, no envelope, no appeal to C7 or C8. A singleton
is the carrier of an internal set, so `loebMeasure_internal` applies to it directly. -/
theorem loebMeasure_singleton (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (x : Ultraproduct U X) :
    loebMeasure hU hX {x} = U.ultralimit fun i ↦ ((Nat.card (X i) : ℝ≥0∞))⁻¹ := by
  induction x using Filter.Product.inductionOn with
  | _ x' =>
    rw [← InternalSet.carrier_ofFun_singleton (U := U) x', loebMeasure_internal,
      internalContent_ofFun]
    exact Ultrafilter.ultralimit_congr
      (Eventually.of_forall fun i ↦ normalizedCounting_singleton (x' i))

/-! ### The growth hypothesis -/

/-- The stage cardinalities grow without bound along `U`.

Stated as "every `n` is eventually a lower bound" rather than as a vanishing ultralimit,
because that is the form applications can check directly from how the stages are given.
`StagesUnbounded.ultralimit_inv_card_eq_zero` converts it. -/
def StagesUnbounded (U : Ultrafilter ι) (X : ι → Type*) : Prop :=
  ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n ≤ Nat.card (X i)

omit [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] in
/-- Unbounded stages make the reciprocal cardinalities vanish in the limit. This is the
"one point per stage is negligible" fact that everything below rests on. -/
theorem StagesUnbounded.ultralimit_inv_card_eq_zero (h : StagesUnbounded U X) :
    U.ultralimit (fun i ↦ ((Nat.card (X i) : ℝ≥0∞))⁻¹) = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) zero_le
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
  rw [zero_add]
  refine ultralimit_le_of_le ?_
  filter_upwards [h n] with i hi
  exact (ENNReal.inv_le_inv.2 (by exact_mod_cast hi)).trans hn.le

/-! ### Internal sets split -/

/-- **Every internal set has an internal half.**

The construction is stagewise and elementary: `Set.exists_subset_card_eq` supplies a
subset of `⌊n / 2⌋` points of each stagewise set. What needs the growth hypothesis is
that the floor is harmless — the bounds `2 * ⌊n / 2⌋ ≤ n ≤ 2 * ⌊n / 2⌋ + 1` differ by one
point of the stage, worth `(Nat.card (X i))⁻¹`, which vanishes in the limit. So the
halving is *exact* in the limit though it is not exact at any stage.

The estimates are carried out on `2 * internalContent U B`, so no `ℝ≥0∞` division appears
until the final rearrangement. -/
theorem exists_internal_le_content_eq_half (hcard : StagesUnbounded U X)
    (A : InternalSet U X) :
    ∃ B : InternalSet U X, B ≤ A ∧ internalContent U B = internalContent U A / 2 := by
  induction A using Filter.Product.inductionOn with
  | _ A' =>
    choose t hts hcardt using fun i ↦
      Set.exists_subset_card_eq (s := A' i) (Nat.div_le_self (A' i).ncard 2)
    refine ⟨Filter.Product.ofFun t,
      (InternalSet.le_ofFun_iff t A').2 (Eventually.of_forall hts), ?_⟩
    have hkey : 2 * internalContent U (Filter.Product.ofFun t : InternalSet U X)
        = internalContent U (Filter.Product.ofFun A' : InternalSet U X) := by
      rw [internalContent_ofFun, internalContent_ofFun,
        ← ultralimit_const_mul (U := U) (by simp : (2 : ℝ≥0∞) ≠ ∞)]
      refine le_antisymm (Ultrafilter.ultralimit_mono (Eventually.of_forall fun i ↦ ?_)) ?_
      · -- `2 * ⌊n / 2⌋ ≤ n`
        rw [normalizedCounting_apply', normalizedCounting_apply', hcardt i,
          ← mul_div_assoc]
        gcongr
        exact_mod_cast Nat.mul_div_le (A' i).ncard 2
      · -- `n ≤ 2 * ⌊n / 2⌋ + 1`, and the stray point vanishes in the limit.
        have hstep : ∀ i, normalizedCounting (X i) (A' i)
            ≤ 2 * normalizedCounting (X i) (t i) + ((Nat.card (X i) : ℝ≥0∞))⁻¹ := by
          intro i
          rw [normalizedCounting_apply', normalizedCounting_apply', hcardt i,
            ← mul_div_assoc, inv_eq_one_div, ENNReal.div_add_div_same]
          gcongr
          have : (A' i).ncard ≤ 2 * ((A' i).ncard / 2) + 1 := by omega
          exact_mod_cast this
        calc U.ultralimit (fun i ↦ normalizedCounting (X i) (A' i))
            ≤ U.ultralimit (fun i ↦ 2 * normalizedCounting (X i) (t i)
                + ((Nat.card (X i) : ℝ≥0∞))⁻¹) :=
              Ultrafilter.ultralimit_mono (Eventually.of_forall hstep)
          _ = U.ultralimit (fun i ↦ 2 * normalizedCounting (X i) (t i)) := by
              rw [ultralimit_add, hcard.ultralimit_inv_card_eq_zero, add_zero]
    rw [ENNReal.eq_div_iff two_ne_zero (by simp : (2 : ℝ≥0∞) ≠ ∞), hkey]

/-! ### Atomlessness -/

/-- **The Loeb measure is atomless when the stages grow.**

This is the statement mathlib's planned `NoAtoms` names, and the one M3 promised. It is
strictly stronger than null singletons, which alone would leave the whole space a
possible atom.

Both earlier results are used: C8 replaces `s` by an internal set agreeing with it almost
everywhere, and `exists_internal_le_content_eq_half` splits that. The witness
`s ∩ B.carrier` then has exactly half the measure of `s`, which is positive and strictly
smaller because a probability measure is finite. -/
theorem exists_measurableSet_subset_measure_lt (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (hcard : StagesUnbounded U X)
    {s : Set (Ultraproduct U X)} (hs : MeasurableSet[loebMeasurableSpace hX] s)
    (hpos : 0 < loebMeasure hU hX s) :
    ∃ t ⊆ s, MeasurableSet[loebMeasurableSpace hX] t ∧
      0 < loebMeasure hU hX t ∧ loebMeasure hU hX t < loebMeasure hU hX s := by
  obtain ⟨A, hA⟩ := (loebMeasurable_iff_internal_mod_null hU hX s).1 hs
  have hae : s =ᵐ[loebMeasure hU hX] InternalSet.carrier A :=
    measure_symmDiff_eq_zero_iff.1 hA
  have hAmeas : loebMeasure hU hX (InternalSet.carrier A) = loebMeasure hU hX s :=
    (measure_congr hae).symm
  obtain ⟨B, hBA, hBval⟩ := exists_internal_le_content_eq_half hcard A
  have hval : loebMeasure hU hX (s ∩ InternalSet.carrier B) = loebMeasure hU hX s / 2 := by
    rw [measure_congr (hae.inter (ae_eq_refl (InternalSet.carrier B))),
      Set.inter_eq_right.2 (InternalSet.carrier_mono hBA), loebMeasure_internal, hBval,
      ← loebMeasure_internal hU hX A, hAmeas]
  exact ⟨s ∩ InternalSet.carrier B, Set.inter_subset_left,
    hs.inter (measurableSet_internal hX B),
    hval ▸ ENNReal.div_pos hpos.ne' (by simp : (2 : ℝ≥0∞) ≠ ∞),
    hval ▸ ENNReal.half_lt_self hpos.ne' (measure_ne_top _ _)⟩

/-- **Null singletons**, the weaker consequence. Proved through the point-mass formula
rather than derived from the splitting theorem, since that route is cheaper and needs no
measurability. -/
theorem nullSingletonClass_loebMeasure (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (hcard : StagesUnbounded U X) :
    NullSingletonClass (loebMeasure hU hX) :=
  ⟨fun x ↦ by
    rw [loebMeasure_singleton hU hX x, hcard.ultralimit_inv_card_eq_zero]⟩

/-- **The hypothesis cannot be dropped.** On stages that are all subsingletons the
ultraproduct carries an atom of full mass, so neither atomlessness nor null singletons
holds.

Compiled rather than asserted, and stated for `Subsingleton` rather than for a specific
family so that it covers every degenerate case at once. This is a counterexample to
dropping the hypothesis, not a converse to the theorems above. -/
theorem loebMeasure_singleton_eq_one_of_subsingleton
    (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hsub : ∀ i, Subsingleton (X i)) (x : Ultraproduct U X) :
    loebMeasure hU hX {x} = 1 := by
  rw [loebMeasure_singleton hU hX x]
  refine (Ultrafilter.ultralimit_congr (Eventually.of_forall fun i ↦ ?_)).trans
    (Ultrafilter.ultralimit_const 1)
  rw [Nat.card_eq_one_iff_unique.2 ⟨hsub i, hX i⟩]
  simp

/-! ### API tests -/

section Tests

/-- **Atomlessness in mathlib's planned `NoAtoms` shape** — the statement M3 promised,
strictly stronger than null singletons. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hcard : StagesUnbounded U X) {s : Set (Ultraproduct U X)}
    (hs : MeasurableSet[loebMeasurableSpace hX] s) (hpos : 0 < loebMeasure hU hX s) :
    ∃ t ⊆ s, MeasurableSet[loebMeasurableSpace hX] t ∧
      0 < loebMeasure hU hX t ∧ loebMeasure hU hX t < loebMeasure hU hX s :=
  exists_measurableSet_subset_measure_lt hU hX hcard hs hpos

/-- **The whole space splits**, which is exactly what null singletons alone would not
give: in the countable–cocountable counterexample the space is an atom. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hcard : StagesUnbounded U X) :
    ∃ t : Set (Ultraproduct U X), MeasurableSet[loebMeasurableSpace hX] t ∧
      0 < loebMeasure hU hX t ∧ loebMeasure hU hX t < 1 := by
  obtain ⟨t, -, hmeas, hpos, hlt⟩ := exists_measurableSet_subset_measure_lt hU hX hcard
    (s := Set.univ) MeasurableSet.univ (by rw [measure_univ]; exact one_pos)
  exact ⟨t, hmeas, hpos, by rwa [measure_univ] at hlt⟩

/-- Internal sets split on their own, with no measurability input. -/
example (hcard : StagesUnbounded U X) (A : InternalSet U X) :
    ∃ B : InternalSet U X, B ≤ A ∧ internalContent U B = internalContent U A / 2 :=
  exists_internal_le_content_eq_half hcard A

/-- Null singletons, used as an instance at the point of use — the `haveI` the docstring
describes. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hcard : StagesUnbounded U X) (x : Ultraproduct U X) :
    loebMeasure hU hX {x} = 0 := by
  haveI := nullSingletonClass_loebMeasure hU hX hcard
  simp

/-- **A concrete instance**: stages `Fin (i + 1)` on the hyperfilter, whose cardinalities
are unbounded because `n ≤ i + 1` for all but finitely many `i`. -/
example (x : Ultraproduct (hyperfilter ℕ) fun i ↦ Fin (i + 1)) :
    loebMeasure Filter.hyperfilter_isCountablyIncomplete (fun _ ↦ ⟨0⟩) {x} = 0 := by
  haveI := nullSingletonClass_loebMeasure Filter.hyperfilter_isCountablyIncomplete
    (X := fun i ↦ Fin (i + 1)) (fun _ ↦ ⟨0⟩) (fun n ↦ by
      have hcof : ∀ᶠ i in (Filter.cofinite : Filter ℕ), n ≤ i + 1 := by
        rw [Nat.cofinite_eq_atTop]
        filter_upwards [Filter.eventually_ge_atTop n] with i hi
        omega
      have hhyp : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), n ≤ i + 1 :=
        Filter.hyperfilter_le_cofinite hcof
      exact hhyp.mono fun i hi ↦ by simpa using hi)
  simp

/-- **The degenerate case really is degenerate**: constant `Unit` stages give an atom of
full mass, so the growth hypothesis is not removable. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    (x : Ultraproduct U fun _ : ℕ ↦ Unit) :
    loebMeasure hU (fun _ ↦ ⟨()⟩) {x} = 1 :=
  loebMeasure_singleton_eq_one_of_subsingleton hU _ (fun _ ↦ inferInstance) x

/-- The point-mass formula itself, on a dependent family. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    (x : Ultraproduct U fun i ↦ Fin (i + 1)) :
    loebMeasure hU (fun _ ↦ ⟨0⟩) {x}
      = U.ultralimit fun i ↦ ((Nat.card (Fin (i + 1)) : ℝ≥0∞))⁻¹ :=
  loebMeasure_singleton hU _ x

end Tests

end Loeb
