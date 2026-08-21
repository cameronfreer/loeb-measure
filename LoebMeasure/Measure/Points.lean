/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.Singleton
import LoebMeasure.Measure.Loeb

/-!
# The measure of a point

The mass of a single point of the ultraproduct, and the null-singleton property that
follows when the stage cardinalities diverge.

## This is not atomlessness

Deliberately a separate module from `LoebMeasure/Measure/Atomless.lean`, and the
separation is mathematical rather than organizational. `MeasureTheory.NullSingletonClass`
is **strictly weaker** than atomlessness: mathlib's own note records that the `NoAtoms` it
plans — every measurable set of positive measure has a measurable subset of strictly
smaller positive measure — implies null singletons but is not implied by them. The
countable–cocountable probability measure separates them, with every singleton null while
the whole space is an atom.

Keeping the two in different files stops the weaker property from occupying the name
"atomless". What is proved here is the point-mass formula and its immediate consequence;
the splitting theorem is next door and needs C7a and C8.

## No approximation is needed

A singleton of the ultraproduct is *already* the carrier of an internal set
(`InternalSet.carrier_singleton`), because eventual stagewise equality is equality in the
ultraproduct. So `loebMeasure_internal` computes a point's measure directly, using none of
C7 or C8 and no splitting argument.

The computation factors cleanly, one step per layer:

```text
InternalSet.singleton  →  internalContent_singleton  →  loebMeasure_singleton
```

## The hypothesis is real

Null singletons need the stage cardinalities to diverge along `U`, written with mathlib's
`Filter.Tendsto _ _ Filter.atTop` rather than a bespoke predicate — the two are the same
statement, and a new name would only add conversion lemmas.

Without it the conclusion is false, not merely unproved: on subsingleton stages the
ultraproduct is one point of mass `1`, which
`loebMeasure_singleton_eq_one_of_subsingleton` records as a compiled statement. That is a
counterexample to dropping the hypothesis, **not** a converse — only the sufficient
direction is proved here, and no equivalence is claimed.

## Why this is a theorem and not an instance

The divergence hypothesis does not appear in `loebMeasure hU hX`, so typeclass inference
cannot recover it — unlike `hU` and `hX`, which do appear and are carried fine. Callers
introduce the conclusion with `haveI`.
-/

namespace Loeb

open Filter MeasureTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] {U : Ultrafilter ι}

/-- **The content of an internal singleton**: the ultralimit of the reciprocal stage
cardinalities.

The middle step of the computation, exposed rather than inlined so that the internal-set
layer and the measure layer each have their own statement. -/
theorem internalContent_singleton (x : Ultraproduct U X) :
    internalContent U (InternalSet.singleton x)
      = U.ultralimit fun i ↦ ((Nat.card (X i) : ℝ≥0∞))⁻¹ := by
  induction x using Filter.Product.inductionOn with
  | _ x' =>
    rw [InternalSet.singleton_ofFun, internalContent_ofFun]
    exact Ultrafilter.ultralimit_congr
      (Eventually.of_forall fun i ↦ normalizedCounting_singleton (x' i))

/-- **The measure of a point** is the ultralimit of the reciprocal stage cardinalities.

A wrapper: a point is a realized internal set, so this is `loebMeasure_internal` applied
to `InternalSet.singleton`. No approximation, no envelope, no appeal to C7 or C8. -/
theorem loebMeasure_singleton (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (x : Ultraproduct U X) :
    loebMeasure hU hX {x} = U.ultralimit fun i ↦ ((Nat.card (X i) : ℝ≥0∞))⁻¹ := by
  rw [← InternalSet.carrier_singleton x, loebMeasure_internal, internalContent_singleton]

/-- **Points are null when the stage cardinalities diverge.**

A theorem rather than an instance: the divergence hypothesis does not appear in
`loebMeasure hU hX`, so typeclass inference cannot recover it. Introduce it with `haveI`
at the use site.

This is *weaker* than atomlessness — see the module docstring, and
`Loeb.exists_measurableSet_subset_measure_lt` for the real thing. -/
theorem nullSingletonClass_loebMeasure (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i))
    (hcard : Tendsto (fun i ↦ Nat.card (X i)) (U : Filter ι) atTop) :
    NullSingletonClass (loebMeasure hU hX) :=
  ⟨fun x ↦ by
    rw [loebMeasure_singleton hU hX x, ultralimit_inv_natCast_eq_zero hcard]⟩

/-- **The hypothesis cannot be dropped.** On stages that are all subsingletons the
ultraproduct carries an atom of full mass, so neither null singletons nor atomlessness
holds.

Compiled rather than asserted, and stated for `Subsingleton` rather than for one specific
family so that it covers every degenerate case at once. It is a counterexample to
dropping the hypothesis, not a converse to the theorem above. -/
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

/-- The point-mass formula. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (x : Ultraproduct U X) :
    loebMeasure hU hX {x} = U.ultralimit fun i ↦ ((Nat.card (X i) : ℝ≥0∞))⁻¹ :=
  loebMeasure_singleton hU hX x

/-- Null singletons, used as an instance at the point of use — the `haveI` the docstring
describes. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hcard : Tendsto (fun i ↦ Nat.card (X i)) (U : Filter ι) atTop)
    (x : Ultraproduct U X) : loebMeasure hU hX {x} = 0 := by
  haveI := nullSingletonClass_loebMeasure hU hX hcard
  simp

/-- **A concrete instance**: stages `Fin (i + 1)` on the hyperfilter. The divergence
hypothesis is mathlib's `Tendsto _ atTop`, so it composes with the usual `atTop` API
rather than needing a bespoke conversion. -/
example (x : Ultraproduct (hyperfilter ℕ) fun i ↦ Fin (i + 1)) :
    loebMeasure Filter.hyperfilter_isCountablyIncomplete (fun _ ↦ ⟨0⟩) {x} = 0 := by
  haveI := nullSingletonClass_loebMeasure Filter.hyperfilter_isCountablyIncomplete
    (X := fun i ↦ Fin (i + 1)) (fun _ ↦ ⟨0⟩) (by
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      exact tendsto_atTop_mono (fun i ↦ Nat.le_succ i)
        (tendsto_id.mono_left (Filter.hyperfilter_le_cofinite.trans_eq
          Nat.cofinite_eq_atTop)))
  simp

/-- **The degenerate case really is degenerate**: constant `Unit` stages give an atom of
full mass, so the divergence hypothesis is not removable. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    (x : Ultraproduct U fun _ : ℕ ↦ Unit) :
    loebMeasure hU (fun _ ↦ ⟨()⟩) {x} = 1 :=
  loebMeasure_singleton_eq_one_of_subsingleton hU _ (fun _ ↦ inferInstance) x

/-- The intermediate content statement, on a dependent family. -/
example (U : Ultrafilter ℕ) (x : Ultraproduct U fun i ↦ Fin (i + 1)) :
    internalContent U (InternalSet.singleton x)
      = U.ultralimit fun i ↦ ((Nat.card (Fin (i + 1)) : ℝ≥0∞))⁻¹ :=
  internalContent_singleton x

end Tests

end Loeb
