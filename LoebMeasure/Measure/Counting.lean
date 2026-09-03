/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.UniformOn

/-!
# Normalized counting measure

The stagewise measures the first Loeb construction is built from.

This is **not a new construction**: mathlib already has it as
`ProbabilityTheory.uniformOn Set.univ`, together with the value formula and a
probability-measure instance for finite nonempty types. `Loeb.normalizedCounting` is a
thin, stable wrapper — introducing a second generic normalized-counting measure would
be a genuine duplication, and the wrapper exists only so the project has one name it
controls for the stage measures.

The definition is polymorphic in a single type and is applied **pointwise** to a family
that varies with the index, which is how the ultraproduct uses it: the stage spaces are
not one fixed type.

## Where nonemptiness is needed, and where it is not

Deliberately split, following ADR-0002:

* the **definition** needs no nonemptiness, and neither does the bound
  `normalizedCounting_le_one` — which in fact needs no *finiteness* either.
  `uniformOn` is `IsZeroOrProbabilityMeasure` unconditionally, so the bound is
  `prob_le_one` outright: on an empty type `univ = ∅` and the measure is `0`, giving
  `0` rather than the `∞` a careless normalization would produce;
* **total mass one**, and hence `IsProbabilityMeasure`, genuinely require `[Nonempty X]`:
  on an empty type the total mass is `0`.

So `[Nonempty X]` appears on the normalization results and nowhere else, and finiteness
appears only in the cardinality formula and the normalization results — never in the
bound.
-/

namespace Loeb

open MeasureTheory
open scoped ENNReal

variable (X : Type*) [MeasurableSpace X]

/-- Counting measure normalized by the cardinality: mathlib's `uniformOn` at `univ`,
under a project-stable name. No nonemptiness is needed to define it; on an empty type
`univ = ∅` and this is the zero measure. -/
noncomputable def normalizedCounting : Measure X :=
  ProbabilityTheory.uniformOn (Set.univ : Set X)

theorem normalizedCounting_eq_uniformOn :
    normalizedCounting X = ProbabilityTheory.uniformOn (Set.univ : Set X) :=
  rfl

variable {X}

theorem normalizedCounting_apply [Fintype X] [MeasurableSingletonClass X] (s : Set X) :
    normalizedCounting X s = (s.ncard : ℝ≥0∞) / (Fintype.card X : ℝ≥0∞) := by
  classical
  rw [normalizedCounting, ProbabilityTheory.uniformOn_univ,
    Measure.count_apply s.toFinite.measurableSet, Set.encard_eq_coe_toFinset_card,
    Set.ncard_eq_toFinset_card' s]
  norm_cast

/-- **Total mass one needs nonemptiness**, and this is where it is needed. Inherited
from mathlib's instance for `uniformOn univ`. -/
instance instIsProbabilityMeasureNormalizedCounting [Finite X] [Nonempty X] :
    IsProbabilityMeasure (normalizedCounting X) :=
  ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ

@[simp]
theorem normalizedCounting_univ [Finite X] [Nonempty X] :
    normalizedCounting X Set.univ = 1 :=
  measure_univ

/-- **The bound needs no nonemptiness.** On an empty type every subset is empty and the
value is `0 / 0 = 0`; the `∞` that a careless normalization would produce never
appears. -/
theorem normalizedCounting_le_one (s : Set X) : normalizedCounting X s ≤ 1 := by
  rw [normalizedCounting_eq_uniformOn]
  exact prob_le_one

/-- The value formula in `Nat.card` form, which is what the ultraproduct layer wants:
the stage spaces carry `[Finite]`, not `[Fintype]`, so a `Fintype.card` statement forces
a `Fintype.ofFinite` at every call site. -/
theorem normalizedCounting_apply_natCard [Finite X] [MeasurableSingletonClass X] (s : Set X) :
    normalizedCounting X s = (s.ncard : ℝ≥0∞) / (Nat.card X : ℝ≥0∞) := by
  classical
  haveI := Fintype.ofFinite X
  rw [normalizedCounting_apply, Nat.card_eq_fintype_card]

/-- The measure of a point: one over the cardinality. -/
theorem normalizedCounting_singleton [Finite X] [MeasurableSingletonClass X] (a : X) :
    normalizedCounting X ({a} : Set X) = ((Nat.card X : ℝ≥0∞))⁻¹ := by
  rw [normalizedCounting_apply_natCard, Set.ncard_singleton, Nat.cast_one, one_div]

/-- **Finiteness needs no nonemptiness either.** `uniformOn` is
`IsZeroOrProbabilityMeasure` unconditionally, so the total mass is `0` or `1` and never
`∞`. Registered as an instance because the integral layer needs it on every stage,
including empty ones. -/
instance instIsFiniteMeasureNormalizedCounting : IsFiniteMeasure (normalizedCounting X) := by
  rw [normalizedCounting_eq_uniformOn]
  infer_instance

/-- The normalized-average form, as a `Finset` sum over the whole type — the shape the
stagewise content computations use. -/
theorem normalizedCounting_apply_eq_sum [Fintype X] [MeasurableSingletonClass X]
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
example [Finite X] [Nonempty X] : normalizedCounting X Set.univ = 1 := by simp

/-- The bound holds with no nonemptiness hypothesis — including on an empty stage. -/
example (s : Set X) : normalizedCounting X s ≤ 1 :=
  normalizedCounting_le_one s

/-- **A varying family of finite types**, which is how the ultraproduct uses this: the
stage spaces are not one fixed type. -/
example (Y : ℕ → Type) [∀ i, MeasurableSpace (Y i)] [∀ i, Fintype (Y i)]
    [∀ i, Nonempty (Y i)] (i : ℕ) :
    normalizedCounting (Y i) Set.univ = 1 := by
  simp

end Tests

end Loeb
