/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.OuterMeasure.Induced

/-!
# Invariance of an induced outer measure under an injective map

Upstream-oriented material: these declarations concern only mathlib objects and live in
mathlib namespaces. See `LoebMeasure/Mathlib/README.md` for the mirror-path convention,
and issue #10 for the upstreaming proposal.

Mathlib's `MeasureTheory.inducedOuterMeasure_preimage` transports an induced outer
measure along a bijection, but it goes through `inducedOuterMeasure_eq_iInf` and so
inherits that lemma's hypotheses: the generating family must be closed under countable
unions, and the generating function must be monotone and countably subadditive on it.
A family that is merely a set ring — such as the realized internal sets of a Loeb
construction — has none of those, yet the invariance still holds, because
`OuterMeasure.map_ofFunction` needs only injectivity.

## Main results

* `MeasureTheory.inducedOuterMeasure_preimage_of_injective`: an injective map that
  preserves the generating family and the generating function preserves the induced
  outer measure of every set.
-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {P : Set α → Prop} {m : ∀ s : Set α, P s → ℝ≥0∞} {P0 : P ∅}
  {m0 : m ∅ P0 = 0}

/-- An injective map that preserves the generating family and the generating function
preserves the induced outer measure of every set. Unlike `inducedOuterMeasure_preimage`,
no closure of `P` under countable unions and no monotonicity or countable subadditivity
of `m` is needed. -/
theorem inducedOuterMeasure_preimage_of_injective {f : α → α} (hf : Function.Injective f)
    (Pm : ∀ s : Set α, P (f ⁻¹' s) ↔ P s)
    (mm : ∀ (s : Set α) (hs : P s), m (f ⁻¹' s) ((Pm _).mpr hs) = m s hs) (A : Set α) :
    inducedOuterMeasure m P0 m0 (f ⁻¹' A) = inducedOuterMeasure m P0 m0 A := by
  have hext : ∀ s, extend m (f ⁻¹' s) = extend m s := fun s ↦
    iInf_congr_Prop (Pm s) fun hs ↦ mm s hs
  rw [← OuterMeasure.map_apply, inducedOuterMeasure, OuterMeasure.map_ofFunction hf]
  simp only [hext]

end MeasureTheory
