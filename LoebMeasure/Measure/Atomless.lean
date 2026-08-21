/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Measure.Loeb

/-!
# Points, and when the Loeb measure is atomless

The measure of a point is the ultralimit of the reciprocal stage cardinalities, and the
Loeb measure is atomless exactly when that ultralimit vanishes.

## No approximation is needed

Atomlessness here costs far less than the usual nonstandard argument, and none of C7 or
C8: a singleton in the ultraproduct is *already* the carrier of an internal set, since

```
{ofFun x} = InternalSet.carrier (ofFun fun i ↦ {x i})
```

— membership on the right is eventual stagewise equality, which is equality in the
ultraproduct (`InternalSet.carrier_ofFun_singleton`). So `loebMeasure_internal` computes
the measure of a point directly from the stage measures. No splitting argument, no
envelope, no approximation.

## The hypothesis is real, not bookkeeping

This Loeb measure is **not** atomless in general. If every stage is a singleton the
ultraproduct is one point of measure `1`, and `loebMeasure_singleton_eq_one_of_subsingleton`
below records that as a compiled statement rather than a remark. Atomlessness needs the
stage cardinalities to grow along `U`, which is `StagesUnbounded`.

That predicate is stated as "every `n` is eventually a lower bound" rather than as a
condition on the ultralimit, because that is the form the applications can check: the
stages are given, and one knows how big they are.

## Why this is a theorem and not an instance

`NullSingletonClass (loebMeasure hU hX)` is proved by `nullSingletonClass_loebMeasure`,
a **theorem** taking `StagesUnbounded U X`. It cannot usefully be an instance: the
cardinality hypothesis does not appear in `loebMeasure hU hX`, so typeclass inference has
no way to recover it. Callers introduce it with `haveI`, and the tests below do exactly
that.

This is the same situation as `hU` and `hX`, which *do* appear in the term and so can be
carried by instances; the contrast is worth noticing when adding further instances to
this measure.

## Scope

Points and atomlessness. The **range** of the Loeb measure — that every internal set of
positive content splits, and more generally that the range is an interval — is a
Lyapunov-type statement about the measure as a whole rather than about points, is
genuinely harder, and is not attempted here.
-/

namespace Loeb

open Filter MeasureTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] {U : Ultrafilter ι}

/-- The stagewise measure of a point: one over the stage cardinality. -/
theorem normalizedCounting_singleton (i : ι) (a : X i) :
    normalizedCounting (X i) ({a} : Set (X i)) = ((Nat.card (X i) : ℝ≥0∞))⁻¹ := by
  classical
  haveI := Fintype.ofFinite (X i)
  rw [normalizedCounting_apply, Set.ncard_singleton, Nat.card_eq_fintype_card, Nat.cast_one,
    one_div]

/-- **The measure of a point** is the ultralimit of the reciprocal stage cardinalities.

Note what is *absent*: no approximation, no envelope, and no appeal to C7 or C8. A
singleton is the carrier of an internal set, so `loebMeasure_internal` applies to it
directly. -/
theorem loebMeasure_singleton (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (x : Ultraproduct U X) :
    loebMeasure hU hX {x} = U.ultralimit fun i ↦ ((Nat.card (X i) : ℝ≥0∞))⁻¹ := by
  induction x using Filter.Product.inductionOn with
  | _ x' =>
    rw [← InternalSet.carrier_ofFun_singleton (U := U) x', loebMeasure_internal,
      internalContent_ofFun]
    exact Ultrafilter.ultralimit_congr
      (Eventually.of_forall fun i ↦ normalizedCounting_singleton i (x' i))

/-! ### Atomlessness -/

/-- The stage cardinalities grow without bound along `U`.

Stated as "every `n` is eventually a lower bound" rather than as a vanishing ultralimit,
because that is the form applications can check directly from how the stages are given.
`StagesUnbounded.ultralimit_inv_card_eq_zero` converts it. -/
def StagesUnbounded (U : Ultrafilter ι) (X : ι → Type*) : Prop :=
  ∀ n : ℕ, ∀ᶠ i in (U : Filter ι), n ≤ Nat.card (X i)

omit [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] in
/-- Unbounded stages make the reciprocal cardinalities vanish in the limit. -/
theorem StagesUnbounded.ultralimit_inv_card_eq_zero (h : StagesUnbounded U X) :
    U.ultralimit (fun i ↦ ((Nat.card (X i) : ℝ≥0∞))⁻¹) = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) zero_le
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
  rw [zero_add]
  refine ultralimit_le_of_le ?_
  filter_upwards [h n] with i hi
  exact (ENNReal.inv_le_inv.2 (by exact_mod_cast hi)).trans hn.le

/-- **The Loeb measure is atomless when the stages grow.**

A theorem rather than an instance: `StagesUnbounded U X` does not appear in
`loebMeasure hU hX`, so typeclass inference cannot recover it. Introduce it with
`haveI` at the use site. -/
theorem nullSingletonClass_loebMeasure (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (hcard : StagesUnbounded U X) :
    NullSingletonClass (loebMeasure hU hX) :=
  ⟨fun x ↦ by
    rw [loebMeasure_singleton hU hX x, hcard.ultralimit_inv_card_eq_zero]⟩

/-- **The hypothesis cannot be dropped.** On stages that are all subsingletons the
ultraproduct carries an atom of full mass.

Compiled rather than asserted, and stated for `Subsingleton` rather than for a specific
family so that it covers every degenerate case at once. -/
theorem loebMeasure_singleton_eq_one_of_subsingleton
    (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hsub : ∀ i, Subsingleton (X i)) (x : Ultraproduct U X) :
    loebMeasure hU hX {x} = 1 := by
  rw [loebMeasure_singleton hU hX x]
  refine (Ultrafilter.ultralimit_congr (Eventually.of_forall fun i ↦ ?_)).trans
    (Ultrafilter.ultralimit_const 1)
  haveI := hsub i
  haveI := hX i
  rw [Nat.card_eq_one_iff_unique.2 ⟨hsub i, hX i⟩]
  simp

/-! ### API tests -/

section Tests

/-- **Atomlessness, used as an instance** at the point of use — the `haveI` the
docstring describes. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hcard : StagesUnbounded U X) (x : Ultraproduct U X) :
    loebMeasure hU hX {x} = 0 := by
  haveI := nullSingletonClass_loebMeasure hU hX hcard
  simp

/-- **A concrete atomless instance**: stages `Fin (i + 1)` on the hyperfilter, whose
cardinalities are unbounded because `n ≤ i + 1` for all but finitely many `i`. -/
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
