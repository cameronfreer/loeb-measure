/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Mathlib.Topology.Compactness.Ultralimit
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Data.Set.Card

/-!
# Ultralimits of probability values

D0.2 spike (issue #2, ADR-0002): ultralimits taken directly in `ℝ≥0∞`, which is
compact Hausdorff with continuous addition, so the generic `Ultrafilter.ultralimit`
API applies with no conversion layer. Stagewise values bounded by `1` have ultralimit
bounded by `1`, hence never `∞`.

The generic compact-ultralimit API this spike produced is **not** here: it concerns
only mathlib objects and lives in the `Ultrafilter` namespace under
`LoebMeasure/Mathlib/Topology/Compactness/Ultralimit.lean` as an independently
upstreamable module. This file keeps the `ℝ≥0∞` specialization and the spike fixture.

The `demoInternalContent` section is the quotient-descent demonstration required by
the spike: a content-like function on `Filter.Product` defined by `Quotient.liftOn`,
with representative independence supplied by `Ultrafilter.ultralimit_congr` — no
canonical representative is ever selected.

Declaration names are provisional until the M3 units land.
-/

namespace Loeb

open Filter Topology
open scoped ENNReal

variable {ι : Type*} {U : Ultrafilter ι} {f g : ι → ℝ≥0∞}

/-- Ultralimits in `ℝ≥0∞` are additive: finite additivity of contents passes through
the limit. -/
theorem ultralimit_add (f g : ι → ℝ≥0∞) :
    U.ultralimit (fun i ↦ f i + g i) = U.ultralimit f + U.ultralimit g :=
  tendsto_nhds_unique (U.tendsto_ultralimit _)
    ((U.tendsto_ultralimit f).add (U.tendsto_ultralimit g))

/-- Eventually-bounded-by-one values have ultralimit bounded by one. -/
theorem ultralimit_le_one (h : ∀ᶠ i in U, f i ≤ 1) : U.ultralimit f ≤ 1 :=
  Ultrafilter.ultralimit_le h

/-- Probability-valued families have finite ultralimit: no accidental `∞`. -/
theorem ultralimit_ne_top (h : ∀ᶠ i in U, f i ≤ 1) : U.ultralimit f ≠ ∞ :=
  (ultralimit_le_one h).trans_lt ENNReal.one_lt_top |>.ne

section DescentDemo

variable (U) (X : ι → Type*) [∀ i, Fintype (X i)]

/-- Demonstration content for the D0.2 spike: the normalized-counting value of a
stagewise family of sets, descended to the dependent filter product by
`Quotient.liftOn`. Representative independence is exactly
`Ultrafilter.ultralimit_congr` applied to the eventual equality of representatives. -/
noncomputable def demoInternalContent
    (A : (U : Filter ι).Product fun i ↦ Set (X i)) : ℝ≥0∞ :=
  Quotient.liftOn A
    (fun A ↦ U.ultralimit fun i ↦ ((A i).ncard : ℝ≥0∞) / (Fintype.card (X i) : ℝ≥0∞))
    fun _ _ h ↦ Ultrafilter.ultralimit_congr (h.mono fun _ hi ↦ by simp only [hi])

/-- On representatives, the demonstration content is the stagewise normalized count's
ultralimit. -/
@[simp]
theorem demoInternalContent_mk (A : ∀ i, Set (X i)) :
    demoInternalContent U X (↑A) =
      U.ultralimit fun i ↦ ((A i).ncard : ℝ≥0∞) / (Fintype.card (X i) : ℝ≥0∞) :=
  rfl

/-- The empty internal set has content zero. -/
theorem demoInternalContent_empty :
    demoInternalContent U X (↑(fun i ↦ (∅ : Set (X i)))) = 0 := by
  simp

/-- The full internal set has content one. Nonempty stages are needed here — this is
the normalization, not the bound. -/
theorem demoInternalContent_univ [∀ i, Nonempty (X i)] :
    demoInternalContent U X (↑(fun i ↦ (Set.univ : Set (X i)))) = 1 := by
  rw [demoInternalContent_mk]
  have h : (fun i ↦ ((Set.univ : Set (X i)).ncard : ℝ≥0∞) / (Fintype.card (X i) : ℝ≥0∞)) =
      fun _ ↦ 1 := by
    funext i
    rw [Set.ncard_univ, Nat.card_eq_fintype_card,
      ENNReal.div_self (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
  rw [h, Ultrafilter.ultralimit_const]

/-- The demonstration content is a probability value. Nonempty stages are *not*
needed: on an empty stage every subset is empty and the ratio is `0 / 0 = 0`, not `∞`.
Nonemptiness is genuinely required only for the normalization
`demoInternalContent_univ`. -/
theorem demoInternalContent_le_one (A : ∀ i, Set (X i)) :
    demoInternalContent U X (↑A) ≤ 1 := by
  rw [demoInternalContent_mk]
  refine ultralimit_le_one (Eventually.of_forall fun i ↦ ?_)
  rcases isEmpty_or_nonempty (X i) with hi | hi
  · simp [Set.eq_empty_of_isEmpty (A i)]
  · rw [ENNReal.div_le_iff (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
      one_mul]
    have hle : (A i).ncard ≤ Fintype.card (X i) := by
      simpa [Set.ncard_univ] using Set.ncard_le_ncard (Set.subset_univ (A i)) Set.finite_univ
    exact_mod_cast hle

end DescentDemo

end Loeb
