/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Normalized counting measure

The stagewise measures the first Loeb construction is built from: mathlib's counting
measure scaled by the reciprocal of the cardinality, on a finite type.

The construction is stated for a **family** of finite types varying with an index, since
that is how the ultraproduct uses it — the stage spaces are not a single fixed type.

## Where nonemptiness is needed, and where it is not

Deliberately split, following ADR-0002:

* the **definition** needs no nonemptiness, and neither does the bound
  `normalizedCounting_le_one`. On an empty type every subset is empty and the value is
  `0 / 0 = 0` in `ℝ≥0∞` — never `∞`, which is the trap this arrangement avoids;
* **total mass one**, and hence `IsProbabilityMeasure`, genuinely require `[Nonempty X]`:
  on an empty type the total mass is `0`.

So `[Nonempty X]` appears on the normalization results and nowhere else.
-/

namespace Loeb

open MeasureTheory
open scoped ENNReal

variable (X : Type*) [MeasurableSpace X] [Fintype X]

/-- Counting measure normalized by the cardinality. No nonemptiness is needed to define
it; on an empty type it is the zero measure. -/
noncomputable def normalizedCounting : Measure X :=
  (Fintype.card X : ℝ≥0∞)⁻¹ • Measure.count

variable {X}

theorem normalizedCounting_apply [MeasurableSingletonClass X] (s : Set X) :
    normalizedCounting X s = (s.ncard : ℝ≥0∞) / (Fintype.card X : ℝ≥0∞) := by
  classical
  rw [normalizedCounting, Measure.smul_apply, smul_eq_mul,
    Measure.count_apply s.toFinite.measurableSet, Set.encard_eq_coe_toFinset_card,
    Set.ncard_eq_toFinset_card' s, ENNReal.div_eq_inv_mul]
  norm_cast

/-- **Total mass one needs nonemptiness**, and this is the only place it is needed. -/
@[simp]
theorem normalizedCounting_univ [Nonempty X] :
    normalizedCounting X Set.univ = 1 := by
  classical
  rw [normalizedCounting, Measure.smul_apply, smul_eq_mul,
    Measure.count_apply MeasurableSet.univ, Set.encard_eq_coe_toFinset_card,
    Set.toFinset_univ, Finset.card_univ,
    show ((Fintype.card X : ℕ∞) : ℝ≥0∞) = (Fintype.card X : ℝ≥0∞) from by norm_cast]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)

instance [Nonempty X] : IsProbabilityMeasure (normalizedCounting X) :=
  ⟨normalizedCounting_univ⟩

/-- **The bound needs no nonemptiness.** On an empty type every subset is empty and the
value is `0 / 0 = 0`; the `∞` that a careless normalization would produce never
appears. -/
theorem normalizedCounting_le_one [MeasurableSingletonClass X] (s : Set X) :
    normalizedCounting X s ≤ 1 := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simp [Set.eq_empty_of_isEmpty s]
  · rw [normalizedCounting_apply,
      ENNReal.div_le_iff (by exact_mod_cast Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _), one_mul]
    have : s.ncard ≤ Fintype.card X := by
      simpa [Set.ncard_univ] using Set.ncard_le_ncard (Set.subset_univ s) Set.finite_univ
    exact_mod_cast this

/-- The normalized-average form, as a `Finset` sum over the whole type — the shape the
stagewise content computations use. -/
theorem normalizedCounting_apply_eq_sum [MeasurableSingletonClass X]
    (s : Set X) [DecidablePred (· ∈ s)] :
    normalizedCounting X s
      = (∑ _x ∈ Finset.univ.filter (· ∈ s), (1 : ℝ≥0∞)) / (Fintype.card X : ℝ≥0∞) := by
  rw [normalizedCounting_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  classical
  rw [Set.ncard_eq_toFinset_card' s]
  congr 1
  ext x
  simp

/-! ### API tests -/

section Tests

/-- A probability measure, when the stage is nonempty. -/
example [Nonempty X] : normalizedCounting X Set.univ = 1 := by simp

/-- The bound holds with no nonemptiness hypothesis — including on an empty stage. -/
example [MeasurableSingletonClass X] (s : Set X) : normalizedCounting X s ≤ 1 :=
  normalizedCounting_le_one s

/-- **A varying family of finite types**, which is how the ultraproduct uses this: the
stage spaces are not one fixed type. -/
example (Y : ℕ → Type) [∀ i, MeasurableSpace (Y i)] [∀ i, Fintype (Y i)]
    [∀ i, Nonempty (Y i)] (i : ℕ) :
    normalizedCounting (Y i) Set.univ = 1 := by
  simp

end Tests

end Loeb
