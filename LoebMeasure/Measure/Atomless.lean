/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Measure.Approximation

/-!
# Atomlessness

Every Loeb measurable set of positive measure has a measurable subset of strictly smaller
positive measure, when the stage cardinalities diverge.

## What atomlessness is, and is not

This is the property mathlib's planned `NoAtoms` names:

```
∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s
```

It is **strictly stronger** than `MeasureTheory.NullSingletonClass`, which lives in
`LoebMeasure/Measure/Points.lean`. Mathlib's own note records that atomlessness implies
null singletons and that the converse fails; the countable–cocountable probability measure
separates them, having every singleton null while the whole space is an atom. Null
singletons therefore do not close this milestone, and the two properties are kept in
different modules so the weaker one cannot occupy the name.

## Splitting is the content

The work is `exists_internal_le_content_eq_half`: every internal set has an internal
*half*. Stagewise, `Set.exists_subset_card_eq` supplies a subset of `⌊n / 2⌋` points. The
floor is what needs the growth hypothesis — `2⌊n/2⌋ ≤ n ≤ 2⌊n/2⌋ + 1` differ by one point
of the stage, worth `(Nat.card (X i))⁻¹`, which vanishes in the limit by
`Loeb.ultralimit_inv_natCast_eq_zero`. So the halving is *exact in the limit* while being
exact at no stage.

The estimates run on `2 * internalContent`, so no `ℝ≥0∞` division appears until the final
rearrangement — truncated subtraction never enters.

The measurable statement then combines this with C8: a measurable set of positive measure
agrees almost everywhere with an internal set, and half of that internal set meets it in a
set of half the measure.

## Hypotheses

Divergence of the stage cardinalities is written with mathlib's
`Filter.Tendsto _ _ Filter.atTop` rather than a bespoke predicate — the two say the same
thing, and a new name would only add conversion lemmas.

It is genuinely needed: on subsingleton stages the ultraproduct is a single atom, which
`Loeb.loebMeasure_singleton_eq_one_of_subsingleton` records. Only the sufficient direction
is proved; that theorem is a counterexample to dropping the hypothesis, not a converse.

`exists_measurableSet_subset_measure_lt` is a theorem, not an instance, for the same
reason as its companion in `Points.lean`: the divergence hypothesis does not appear in
`loebMeasure hU hX`, so typeclass inference cannot recover it.

## Scope

Splitting into halves, and the resulting atomlessness. The full **Lyapunov** statement —
that the range of the measure is all of `[0, 1]`, not merely that it contains a strictly
intermediate value — needs iterating the split and a limit argument, and is not attempted
here.
-/

namespace Loeb

open Filter MeasureTheory
open scoped ENNReal symmDiff

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] {U : Ultrafilter ι}

/-- **Every internal set has an internal half.**

Stagewise and elementary, apart from the rounding: `Set.exists_subset_card_eq` supplies
`⌊n / 2⌋` points of each stagewise set, and the growth hypothesis is exactly what makes
the discarded point per stage negligible in the limit.

Note this is a statement about internal sets and their content alone — no measurable sets,
no `loebMeasure`, and no approximation. -/
theorem exists_internal_le_content_eq_half
    (hcard : Tendsto (fun i ↦ Nat.card (X i)) (U : Filter ι) atTop) (A : InternalSet U X) :
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
              rw [ultralimit_add, ultralimit_inv_natCast_eq_zero hcard, add_zero]
    rw [ENNReal.eq_div_iff two_ne_zero (by simp : (2 : ℝ≥0∞) ≠ ∞), hkey]

/-- **The Loeb measure is atomless when the stage cardinalities diverge.**

The statement M3 promised, in mathlib's planned `NoAtoms` shape, and strictly stronger
than the null singletons of `LoebMeasure/Measure/Points.lean`.

Both inputs are used once: C8 replaces `s` by an almost-everywhere equal internal set, and
`exists_internal_le_content_eq_half` splits that. The witness `s ∩ B.carrier` has exactly
half the measure of `s`, which is positive and strictly smaller because a probability
measure is finite. -/
theorem exists_measurableSet_subset_measure_lt (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i))
    (hcard : Tendsto (fun i ↦ Nat.card (X i)) (U : Filter ι) atTop)
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
    hval ▸ ENNReal.div_pos hpos.ne' (by simp),
    hval ▸ ENNReal.half_lt_self hpos.ne' (measure_ne_top _ _)⟩

/-! ### API tests -/

section Tests

variable (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
  (hcard : Tendsto (fun i ↦ Nat.card (X i)) (U : Filter ι) atTop)

/-- **Atomlessness in mathlib's planned `NoAtoms` shape** — the statement M3 promised. -/
example {s : Set (Ultraproduct U X)} (hs : MeasurableSet[loebMeasurableSpace hX] s)
    (hpos : 0 < loebMeasure hU hX s) :
    ∃ t ⊆ s, MeasurableSet[loebMeasurableSpace hX] t ∧
      0 < loebMeasure hU hX t ∧ loebMeasure hU hX t < loebMeasure hU hX s :=
  exists_measurableSet_subset_measure_lt hU hX hcard hs hpos

/-- **The whole space splits**, which is exactly what null singletons alone would not
give: in the countable–cocountable counterexample the space is an atom. -/
example : ∃ t : Set (Ultraproduct U X), MeasurableSet[loebMeasurableSpace hX] t ∧
      0 < loebMeasure hU hX t ∧ loebMeasure hU hX t < 1 := by
  obtain ⟨t, -, hmeas, hpos, hlt⟩ := exists_measurableSet_subset_measure_lt hU hX hcard
    (s := Set.univ) MeasurableSet.univ (by rw [measure_univ]; exact one_pos)
  exact ⟨t, hmeas, hpos, by rwa [measure_univ] at hlt⟩

/-- Internal sets split on their own, with no measurability input and no `loebMeasure`. -/
example (A : InternalSet U X) :
    ∃ B : InternalSet U X, B ≤ A ∧ internalContent U B = internalContent U A / 2 :=
  exists_internal_le_content_eq_half hcard A

/-- **A genuinely dependent family** of stages, where the split is not uniform across
stages — `Fin (i + 1)` alternates between odd and even cardinality, so the floor in
`⌊n / 2⌋` is discarding a point at infinitely many stages. -/
example (U : Ultrafilter ℕ)
    (hcard : Tendsto (fun i ↦ Nat.card (Fin (i + 1))) (U : Filter ℕ) atTop)
    (A : InternalSet U fun i ↦ Fin (i + 1)) :
    ∃ B : InternalSet U fun i ↦ Fin (i + 1), B ≤ A ∧
      internalContent U B = internalContent U A / 2 :=
  exists_internal_le_content_eq_half hcard A

end Tests

end Loeb
