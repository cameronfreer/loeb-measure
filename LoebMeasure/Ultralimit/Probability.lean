/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Mathlib.Topology.Compactness.Ultralimit
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Probability ultralimits

The `ℝ≥0∞` specialization of the ultralimit API: the arithmetic and bounds that internal
content needs.

Everything here is built on `Ultrafilter.ultralimit` from
`LoebMeasure/Mathlib/Topology/Compactness/Ultralimit.lean`. There is no second
definition, and `Ultrafilter.lim` is never unfolded — the generic API is used
exclusively, so if it changes these results follow rather than break.

## Why `ℝ≥0∞`

ADR-0002. At the pinned revision `ℝ≥0∞` is a compact Hausdorff order topology with
continuous addition, and it is already the `MeasureTheory.AddContent` codomain, so no
conversion layer appears anywhere in the content pipeline. Nonemptiness of stage spaces
is needed for probability *normalization*, not for boundedness — which is why no
nonemptiness hypothesis appears below.

## Scope

Arithmetic and bounds only. Quotient descent, internal sets, counting measures, and the
Carathéodory construction are all downstream and are deliberately absent; the descent
shape in particular belongs with `internalContent` when that is defined.
-/

namespace Loeb

open Filter Topology
open scoped ENNReal

variable {ι : Type*} {U : Ultrafilter ι} {f g : ι → ℝ≥0∞}

/-! ### Constants -/

@[simp]
theorem ultralimit_zero : U.ultralimit (fun _ ↦ (0 : ℝ≥0∞)) = 0 :=
  Ultrafilter.ultralimit_const 0

@[simp]
theorem ultralimit_one : U.ultralimit (fun _ ↦ (1 : ℝ≥0∞)) = 1 :=
  Ultrafilter.ultralimit_const 1

/-! ### Arithmetic -/

/-- Ultralimits are additive: finite additivity of a content passes through the limit.
This is continuity of addition on `ℝ≥0∞`, which is unconditional there. -/
theorem ultralimit_add (f g : ι → ℝ≥0∞) :
    U.ultralimit (fun i ↦ f i + g i) = U.ultralimit f + U.ultralimit g :=
  tendsto_nhds_unique (U.tendsto_ultralimit _)
    ((U.tendsto_ultralimit f).add (U.tendsto_ultralimit g))

/-- **Ultralimits commute with scaling by a finite constant.**

`c ≠ ∞` is genuinely needed and is not an artifact: `(∞ * ·)` is discontinuous at `0`,
since `∞ * 0 = 0` while `∞ * x = ∞` nearby. At `c = 0` the map is constantly `0` — using
`0 * ∞ = 0` — and so continuous, which is why the hypothesis is `≠ ∞` rather than the
more familiar `0 < c < ∞`. -/
theorem ultralimit_const_mul {c : ℝ≥0∞} (hc : c ≠ ∞) (f : ι → ℝ≥0∞) :
    U.ultralimit (fun i ↦ c * f i) = c * U.ultralimit f :=
  Ultrafilter.ultralimit_comp (g := (c * ·)) (ENNReal.continuous_const_mul hc) U f

/-! ### Bounds

Stated with **eventual** hypotheses, the weakest useful form, with pointwise corollaries
where they save a wrapper at the call site. -/

/-- An eventual bound bounds the ultralimit. -/
theorem ultralimit_le_of_le {b : ℝ≥0∞} (h : ∀ᶠ i in U, f i ≤ b) : U.ultralimit f ≤ b :=
  Ultrafilter.ultralimit_le h

theorem ultralimit_le_one (h : ∀ᶠ i in U, f i ≤ 1) : U.ultralimit f ≤ 1 :=
  ultralimit_le_of_le h

theorem ultralimit_le_one' (h : ∀ i, f i ≤ 1) : U.ultralimit f ≤ 1 :=
  ultralimit_le_one (Eventually.of_forall h)

/-- **No accidental `∞`.** Derived from the bound rather than from any extra
hypothesis — in particular no nonemptiness is needed. -/
theorem ultralimit_ne_top_of_le {b : ℝ≥0∞} (hb : b ≠ ∞) (h : ∀ᶠ i in U, f i ≤ b) :
    U.ultralimit f ≠ ∞ :=
  ((ultralimit_le_of_le h).trans_lt (Ne.lt_top hb)).ne

theorem ultralimit_ne_top (h : ∀ᶠ i in U, f i ≤ 1) : U.ultralimit f ≠ ∞ :=
  ultralimit_ne_top_of_le ENNReal.one_ne_top h

/-! ### Vanishing reciprocals -/

/-- **Reciprocals of a diverging natural family vanish in the limit.**

Stated for an arbitrary `n : ι → ℕ` rather than for stage cardinalities: the measure
layer uses it twice, once for the mass of a point and once for the rounding error in the
internal halving, and neither use is about the stages as such. -/
theorem ultralimit_inv_natCast_eq_zero {n : ι → ℕ}
    (hn : Tendsto n (U : Filter ι) atTop) :
    U.ultralimit (fun i ↦ ((n i : ℝ≥0∞))⁻¹) = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) zero_le
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
  rw [zero_add]
  refine ultralimit_le_of_le ?_
  filter_upwards [hn.eventually_ge_atTop k] with i hi
  exact (ENNReal.inv_le_inv.2 (by exact_mod_cast hi)).trans hk.le

/-! ### API tests -/

section Tests

/-- Constants, by `simp`, through the generic rule. -/
example : U.ultralimit (fun _ ↦ (1 : ℝ≥0∞)) = 1 := by simp

/-- Additivity is the form finite additivity of a content will use. -/
example (f g : ι → ℝ≥0∞) :
    U.ultralimit (fun i ↦ f i + g i) = U.ultralimit f + U.ultralimit g :=
  ultralimit_add f g

/-- A probability-valued family stays in `[0, 1]` and never reaches `∞`. -/
example (h : ∀ᶠ i in U, f i ≤ 1) : U.ultralimit f ≤ 1 ∧ U.ultralimit f ≠ ∞ :=
  ⟨ultralimit_le_one h, ultralimit_ne_top h⟩

/-- The eventual hypothesis is genuinely weaker: a family bounded only on a large set
still has bounded ultralimit. -/
example {s : Set ι} (hs : s ∈ U) (h : ∀ i ∈ s, f i ≤ 1) : U.ultralimit f ≤ 1 :=
  ultralimit_le_one (Filter.eventually_of_mem hs h)

end Tests

end Loeb
