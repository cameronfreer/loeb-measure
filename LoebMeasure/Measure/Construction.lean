/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.Saturation
import LoebMeasure.Measure.Packaging

/-!
# Sigma-subadditivity of the internal content

The last hypothesis the Carathéodory extension needs, on the route accepted in
ADR-0003:

```text
M2's eventually_eq_bot_of_antitone_iInter_carrier_eq_empty
  ↓  continuity at ∅
MeasureTheory.addContent_iUnion_eq_sum_of_tendsto_zero
  ↓  countable additivity on the ring
MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum
```

## Why saturation makes this cheap

Continuity at `∅` is usually a limit argument. Here it is not: a decreasing sequence of
internal sets whose carriers meet emptily is **eventually `⊥`**, so the contents are
eventually `0` and the convergence is trivial. That is exactly what M2's saturation
theorem provides, and it is why the M2/M3 scope boundary was drawn where it was.

## Hypotheses

Countable incompleteness enters the measure layer here for the first time, as an
explicit argument `(hU : (U : Filter ι).IsCountablyIncomplete)` matching M2's convention,
alongside `(hX : ∀ i, Nonempty (X i))` from the carrier transport.

Note this consumes I6's saturation *consequence*, not I5's diagonal-selection API: the
selection theorem's public shape is never exercised here.
-/

namespace Loeb

open Filter MeasureTheory Topology
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] {U : Ultrafilter ι} {s : ℕ → Set (Ultraproduct U X)}

/-- The content is finite on the ring — one of the two inputs to
`addContent_iUnion_eq_sum_of_tendsto_zero`. -/
theorem internalAddContent_ne_top (hX : ∀ i, Nonempty (X i)) {t : Set (Ultraproduct U X)}
    (ht : t ∈ InternalSet.carriers U X) : internalAddContent hX t ≠ ∞ := by
  obtain ⟨A, rfl⟩ := ht
  rw [internalAddContent_carrier]
  exact internalContent_ne_top A

omit [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] in
/-- Carrier inclusion reflects the internal order. Needs no measure-theoretic structure
— it is faithfulness plus the Boolean order.

`private`: its only consumer is the antitone reflection below. C4's carrier-disjointness
conversion does *not* factor through it — that goes directly through `carrier_injective`
on an equality — so it has one consumer, not two. Should a second appear, the public
form belongs in `Loeb.InternalSet` beside `carrier_injective`. -/
private theorem le_of_carrier_subset (hX : ∀ i, Nonempty (X i)) {A B : InternalSet U X}
    (h : InternalSet.carrier A ⊆ InternalSet.carrier B) : A ≤ B := by
  have hsup : InternalSet.carrier (A ⊔ B) = InternalSet.carrier B := by
    rw [InternalSet.carrier_sup]
    exact Set.union_eq_self_of_subset_left h
  exact sup_eq_right.1 (InternalSet.carrier_injective hX hsup)

/-- **Continuity at `∅`.** A decreasing sequence in the ring with empty intersection has
contents tending to zero — and, by saturation, they are eventually *equal* to zero. -/
theorem internalAddContent_tendsto_zero (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (hs : ∀ n, s n ∈ InternalSet.carriers U X)
    (hanti : Antitone s) (hempty : ⋂ n, s n = ∅) :
    Tendsto (fun n ↦ internalAddContent hX (s n)) atTop (𝓝 0) := by
  classical
  -- Choose representing internal sets locally; no global inverse to `carrier` is exposed.
  choose A hA using hs
  have hantiA : Antitone A := by
    intro m n hmn
    exact le_of_carrier_subset hX (by rw [hA m, hA n]; exact hanti hmn)
  have hemptyA : ⋂ n, InternalSet.carrier (A n) = ∅ := by
    rw [← hempty]; exact Set.iInter_congr hA
  have hbot := InternalSet.eventually_eq_bot_of_antitone_iInter_carrier_eq_empty hU hX
    hantiA hemptyA
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hbot] with n hn
  rw [← hA n, internalAddContent_carrier, hn, internalContent_bot]

/-- Countable additivity on the ring, from continuity at `∅`. -/
theorem internalAddContent_iUnion_eq_tsum (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) ⦃f : ℕ → Set (Ultraproduct U X)⦄
    (hf : ∀ i, f i ∈ InternalSet.carriers U X)
    (hUf : (⋃ i, f i) ∈ InternalSet.carriers U X) (hdisj : Pairwise (Function.onFun Disjoint f)) :
    internalAddContent hX (⋃ i, f i) = ∑' i, internalAddContent hX (f i) :=
  addContent_iUnion_eq_sum_of_tendsto_zero InternalSet.isSetRing_carriers _
    (fun _ ht ↦ internalAddContent_ne_top hX ht)
    (fun _ hs hanti hempty ↦ internalAddContent_tendsto_zero hU hX hs hanti hempty)
    hf hUf hdisj

/-- **The internal content is σ-subadditive** — the last input the Carathéodory
extension needs. -/
theorem internalAddContent_isSigmaSubadditive (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) :
    (internalAddContent (U := U) (X := X) hX).IsSigmaSubadditive :=
  isSigmaSubadditive_of_addContent_iUnion_eq_tsum InternalSet.isSetRing_carriers
    fun _ hf hUf hdisj ↦ internalAddContent_iUnion_eq_tsum hU hX hf hUf hdisj

/-! ### API tests -/

section Tests

/-- **The interface C6 needs**: the σ-subadditivity hypothesis of
`AddContent.measureCaratheodory`. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i)) :
    (internalAddContent (U := U) (X := X) hX).IsSigmaSubadditive :=
  internalAddContent_isSigmaSubadditive hU hX

/-- Continuity at `∅`, the substance of the route. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hs : ∀ n, s n ∈ InternalSet.carriers U X) (hanti : Antitone s)
    (hempty : ⋂ n, s n = ∅) :
    Tendsto (fun n ↦ internalAddContent hX (s n)) atTop (𝓝 0) :=
  internalAddContent_tendsto_zero hU hX hs hanti hempty

/-- **Countable additivity on the ring**, tested directly rather than only through its
σ-subadditive consequence: it is the milestone's countable-additivity result and part of
the public surface. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (f : ℕ → Set (Ultraproduct U X)) (hf : ∀ i, f i ∈ InternalSet.carriers U X)
    (hUf : (⋃ i, f i) ∈ InternalSet.carriers U X)
    (hdisj : Pairwise (Function.onFun Disjoint f)) :
    internalAddContent hX (⋃ i, f i) = ∑' i, internalAddContent hX (f i) :=
  internalAddContent_iUnion_eq_tsum hU hX hf hUf hdisj

/-- Finiteness on the ring, the other constructor input. -/
example (hX : ∀ i, Nonempty (X i)) (A : InternalSet U X) :
    internalAddContent hX (InternalSet.carrier A) ≠ ∞ :=
  internalAddContent_ne_top hX ⟨A, rfl⟩

/-- **A genuinely dependent family**, at the canonical hyperfilter — where countable
incompleteness is available rather than hypothetical. -/
example (hX : ∀ i, Nonempty (Fin (i + 1))) :
    (internalAddContent (U := Filter.hyperfilter ℕ) (X := fun i ↦ Fin (i + 1))
      hX).IsSigmaSubadditive :=
  internalAddContent_isSigmaSubadditive Filter.hyperfilter_isCountablyIncomplete hX

end Tests

end Loeb
