/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Integral.Characteristic
import LoebMeasure.Measure.Loeb

/-!
# Measurability of the lift

The lift of a uniformly bounded internal map is measurable for the Loeb σ-algebra.

## The σ-algebra, not the measure

This is where `loebMeasurableSpace` enters M5 — and **only** the σ-algebra.
`loebMeasure` and `hU` do not appear anywhere in this module: measurability is a statement
about which sets are measurable, and countable incompleteness has nothing to do with it.
That mirrors M3, where `loebMeasurableSpace` itself takes only `hX`. The measure arrives at
F3.

What does arrive here, for the first time in M5, are the finite-discrete stage instances,
through `measurableSet_internal`.

## Sublevel sets are countable intersections of carriers

The content is `lift_preimage_Iic`:

```
lift f ⁻¹' Set.Iic r = ⋂ n, InternalSet.carrier (f.strictSublevel (r + 1 / (n + 1)))
```

A sublevel set of the lift **need not be internal** — that is the difficulty, though it is
not always so: a constant lift has sublevel sets `∅` or `univ`, both internal. What is
always true, and what the σ-algebra needs, is that it is a countable intersection of
internal carriers, which the Carathéodory σ-algebra is closed under.
`measurableSet_internal` supplies each piece.

Both inclusions run through F1a's `tendsto_lift_ofFun`, so **boundedness is load-bearing**
for the characterization and hence for measurability — not inherited bookkeeping.
(F1b's arithmetic already used it for the same reason, to obtain algebraic identities from
convergence; this is not the first such use.)

* forwards, a limit `≤ r` is *strictly* below `r + 1/(n+1)`, and convergence turns that
  into an eventual strict stagewise inequality — which is carrier membership;
* backwards, eventual membership at every `n` bounds the limit by `r + 1/(n+1)` for every
  `n`, and `exists_nat_one_div_lt` closes the gap to `≤ r`.

The **strict** stagewise threshold is deliberate. Convergence yields eventual strict
inequality below a strict bound; a non-strict threshold would not follow from it.

`lift_preimage_Iic` is stated on the internal map, through `strictSublevel`, so no chosen
representative appears in the public statement. It is a plain theorem and **not** `@[simp]`:
expanding a preimage into an infinite intersection is not a normal form anyone wants.

## Scope

Measurability. The integral identity is F3, and no `L¹`/`L∞` structure is built here.
-/

namespace Loeb

open Filter MeasureTheory Topology

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] {U : Ultrafilter ι}

namespace InternalMap

/-- **The stagewise strict sublevel set** of an internal map: internally, the points where
the stagewise function is below `r`.

Built by `Filter.Product.map`, so no representative is chosen and there is no
well-definedness obligation — which is what lets `lift_preimage_Iic` be stated without
exposing one. -/
def strictSublevel (f : InternalMap U X fun _ ↦ ℝ) (r : ℝ) : InternalSet U X :=
  Filter.Product.map (fun _ g ↦ {x | g x < r}) f

omit [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] in
@[simp]
theorem strictSublevel_ofFun (g : (i : ι) → X i → ℝ) (r : ℝ) :
    strictSublevel (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ) r
      = Filter.Product.ofFun fun i ↦ {x | g i x < r} :=
  Filter.Product.map_ofFun _ _

omit [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] in
/-- **The sublevel sets of the lift are countable intersections of internal carriers.**

The mathematical content of F2, and stated separately from the measurability corollary
because a later approximation argument will want it.

Deliberately not `@[simp]`: rewriting a preimage into an infinite intersection is not a
useful normal form.

Takes **no stage instances at all** — not even measurability. It is a statement about the
lift and about carriers, and the measurable structure is needed only to conclude that those
carriers are measurable, which happens in `measurable_lift`. -/
theorem lift_preimage_Iic {f : InternalMap U X fun _ ↦ ℝ} (hf : f.IsUniformlyBounded)
    (r : ℝ) :
    lift f ⁻¹' Set.Iic r
      = ⋂ n : ℕ, InternalSet.carrier (f.strictSublevel (r + 1 / (n + 1 : ℝ))) := by
  induction f using Filter.Product.inductionOn with
  | _ g =>
    obtain ⟨C, hC⟩ := (isUniformlyBounded_ofFun g).1 hf
    have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1 : ℝ) := fun n ↦ by positivity
    ext x
    induction x using Filter.Product.inductionOn with
    | _ x' =>
      -- Bound once, through F1a's API, and use it for both directions.
      have htend := tendsto_lift_ofFun hC x'
      rw [lift_ofFun] at htend
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, strictSublevel_ofFun,
        InternalSet.mem_carrier_ofFun, Set.mem_setOf_eq, lift_ofFun]
      constructor
      · -- A limit at most `r` is strictly below `r + 1/(n+1)`, so eventually the values are.
        intro hle n
        exact htend.eventually_lt_const (by linarith [hpos n])
      · -- Eventual membership at every `n` bounds the limit by every `r + 1/(n+1)`.
        intro hmem
        by_contra hgt
        push Not at hgt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hgt)
        have hbound := le_of_tendsto htend ((hmem n).mono fun _ hi ↦ hi.le)
        linarith

/-- **The lift of a uniformly bounded internal map is Loeb measurable.**

Takes `hX` and the stage instances, and **not** `hU`: this is a statement about the
σ-algebra, which needs no countable incompleteness. -/
theorem measurable_lift (hX : ∀ i, Nonempty (X i)) {f : InternalMap U X fun _ ↦ ℝ}
    (hf : f.IsUniformlyBounded) :
    Measurable[loebMeasurableSpace hX] (lift f) := by
  refine measurable_of_Iic (fun r ↦ ?_)
  rw [lift_preimage_Iic hf]
  exact MeasurableSet.iInter fun n ↦ measurableSet_internal hX _

end InternalMap

/-- The bundled form: a wrapper on `InternalMap.measurable_lift`. -/
theorem BoundedInternalFunction.measurable_lift (hX : ∀ i, Nonempty (X i))
    (f : BoundedInternalFunction U X) :
    Measurable[loebMeasurableSpace hX] f.lift :=
  InternalMap.measurable_lift hX f.2

/-! ### API tests -/

section Tests

variable (hX : ∀ i, Nonempty (X i))

/-- The quotient-level statement, with no representative in sight. -/
example {f : InternalMap U X fun _ ↦ ℝ} (hf : f.IsUniformlyBounded) :
    Measurable[loebMeasurableSpace hX] (InternalMap.lift f) :=
  InternalMap.measurable_lift hX hf

/-- And the bundled wrapper. -/
example (f : BoundedInternalFunction U X) :
    Measurable[loebMeasurableSpace hX] f.lift :=
  f.measurable_lift hX

/-- **Indicator consistency, route one**: through the general theorem. -/
example (A : InternalSet U X) :
    Measurable[loebMeasurableSpace hX] (InternalMap.lift (InternalSet.indicatorMap A)) :=
  InternalMap.measurable_lift hX (InternalSet.isUniformlyBounded_indicatorMap A)

/-- **Indicator consistency, route two**: through F1b's set bridge and M3's
`measurableSet_internal`, with no appeal to F2's sublevel argument.

Both routes must land on the same statement — this is E5's characteristic-function
commitment at the measurability level, compiled rather than asserted. -/
example (A : InternalSet U X) :
    Measurable[loebMeasurableSpace hX] (InternalMap.lift (InternalSet.indicatorMap A)) := by
  have h : InternalMap.lift (InternalSet.indicatorMap A)
      = Set.indicator (InternalSet.carrier A) fun _ ↦ (1 : ℝ) := by
    funext x
    exact InternalSet.lift_indicatorMap A x
  rw [h]
  exact (measurable_const.indicator (measurableSet_internal hX A))

/-- The sublevel identity on its own, which a later approximation argument will want. -/
example {f : InternalMap U X fun _ ↦ ℝ} (hf : f.IsUniformlyBounded) (r : ℝ) :
    InternalMap.lift f ⁻¹' Set.Iic r
      = ⋂ n : ℕ, InternalSet.carrier (f.strictSublevel (r + 1 / (n + 1 : ℝ))) :=
  InternalMap.lift_preimage_Iic hf r

/-- **A genuinely dependent family** of stage types. -/
example (U : Ultrafilter ℕ) (g : (i : ℕ) → Fin (i + 1) → ℝ)
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ x, ‖g i x‖ ≤ 1) :
    Measurable[loebMeasurableSpace (fun _ ↦ ⟨0⟩)]
      (InternalMap.lift (Filter.Product.ofFun g :
        InternalMap U (fun i ↦ Fin (i + 1)) fun _ ↦ ℝ)) :=
  InternalMap.measurable_lift _ ⟨1, h⟩

end Tests

end Loeb
