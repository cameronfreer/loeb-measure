/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Integral.Mean

/-!
# Internal step maps

Finite linear combinations of internal indicators, and the integral identity for them.

## Why a named combination rather than instances

`InternalMap.stepMap` is built by finite recursion from `add`, `constMul` and
`InternalSet.indicatorMap`. No global `Add` or `SMul` instance on `InternalMap` is
introduced merely to write a sum: the combination is the only thing needed, so it is what
gets a name.

The list is the **codebook**: a finite *list* of coefficients paired with internal sets,
fixed independently of the stage. A list rather than a set — `stepMap` permits duplicate
entries, and their contributions add. That is what makes the approximation in
`LoebMeasure/Integral/Identity.lean` usable — a per-stage finite range would be automatic,
since each `X i` is finite, and would say nothing.

## Hypotheses, layer by layer

The step layer stratifies further than expected, and the sections record it:

* the construction and the **value** side — `stepMap`, its boundedness, and `lift_stepMap`
  — take **no stage instances at all**, not even `MeasurableSpace`;
* `internalMean_zeroMap` needs `MeasurableSpace`, since the stage measures do;
* the **mean** side and the integral identity need the finite discrete structure, through
  `internalMean_indicatorMap`;
* only `integral_lift_stepMap` mentions `loebMeasure`, `hU` or `hX`.
-/

namespace Loeb

open Filter MeasureTheory

variable {ι : Type*} {X : ι → Type*} {U : Ultrafilter ι}

namespace InternalMap

/-- The zero internal map. -/
def zeroMap : InternalMap U X fun _ ↦ ℝ := Filter.Product.ofFun fun _ _ ↦ 0

/-- The zero map lifts to the zero function. -/
@[simp]
theorem lift_zeroMap (x : Ultraproduct U X) : lift (zeroMap : InternalMap U X fun _ ↦ ℝ) x = 0 := by
  induction x using Filter.Product.inductionOn with
  | _ x' => simp [zeroMap]

/-- The zero map is uniformly bounded, by `0`. -/
theorem isUniformlyBounded_zeroMap :
    (zeroMap : InternalMap U X fun _ ↦ ℝ).IsUniformlyBounded :=
  ⟨0, Eventually.of_forall fun _ _ ↦ by simp⟩

/-- **A finite linear combination of internal indicators.**

The list is a codebook fixed independently of the stage. It is a list rather than a set:
duplicate entries are permitted and their contributions add. Built by recursion from
`add`, `constMul` and `indicatorMap` rather than through an algebraic instance. -/
noncomputable def stepMap : List (ℝ × InternalSet U X) → InternalMap U X fun _ ↦ ℝ
  | [] => zeroMap
  | p :: t => add (constMul p.1 (InternalSet.indicatorMap p.2)) (stepMap t)

/-- The empty codebook gives the zero map. -/
@[simp]
theorem stepMap_nil : stepMap ([] : List (ℝ × InternalSet U X)) = zeroMap := rfl

/-- Consing onto the codebook adds one scaled indicator. -/
@[simp]
theorem stepMap_cons (p : ℝ × InternalSet U X) (t : List (ℝ × InternalSet U X)) :
    stepMap (p :: t) = add (constMul p.1 (InternalSet.indicatorMap p.2)) (stepMap t) := rfl

/-- **Step maps are uniformly bounded.** By recursion: indicators are bounded by `1`,
scaling multiplies the bound, and addition adds it. -/
theorem isUniformlyBounded_stepMap (l : List (ℝ × InternalSet U X)) :
    (stepMap l).IsUniformlyBounded := by
  induction l with
  | nil => exact isUniformlyBounded_zeroMap
  | cons p t ih =>
    exact ((InternalSet.isUniformlyBounded_indicatorMap p.2).constMul p.1).add ih

/-- **The value of a step map**: the corresponding combination of carrier indicators. -/
theorem lift_stepMap (l : List (ℝ × InternalSet U X)) (x : Ultraproduct U X) :
    lift (stepMap l) x
      = (l.map fun p ↦ p.1 * Set.indicator (InternalSet.carrier p.2) (fun _ ↦ (1 : ℝ)) x).sum := by
  induction l with
  | nil => simp
  | cons p t ih =>
    rw [stepMap_cons, lift_add ((InternalSet.isUniformlyBounded_indicatorMap p.2).constMul p.1)
      (isUniformlyBounded_stepMap t), lift_constMul p.1
      (InternalSet.isUniformlyBounded_indicatorMap p.2), InternalSet.lift_indicatorMap, ih]
    simp

/-- **The representative computation rule** for a step map built from represented internal
sets.

The first check that the `List` codebook serves the quantizer F3b-ii needs: it reduces a
step map to an explicit stagewise finite sum, which is the form the error estimate will be
made against.

Marked `@[simp]`, but with a caveat worth knowing: the left-hand side is
`stepMap (l.map fun p ↦ (p.1, ofFun p.2))`, and `simp`'s own `List.map_map` fuses that
outer map into any map producing `l`, dissolving the pattern before this rule can fire. So
it applies when a goal already has this literal shape, and a codebook assembled as a single
`map` over an index type — the shape the quantizer produces — needs the rule instantiated by
hand first. The test below does exactly that. -/
@[simp]
theorem stepMap_ofFun (l : List (ℝ × ((i : ι) → Set (X i)))) :
    stepMap (l.map fun p ↦ (p.1, (Filter.Product.ofFun p.2 : InternalSet U X)))
      = Filter.Product.ofFun fun i y ↦
          (l.map fun p ↦ p.1 * Set.indicator (p.2 i) (fun _ ↦ (1 : ℝ)) y).sum := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    rw [List.map_cons, stepMap_cons, ih, InternalSet.indicatorMap_ofFun, constMul_ofFun,
      add_ofFun]
    rfl

section Stage

variable [∀ i, MeasurableSpace (X i)]

/-- The zero map has zero mean. -/
@[simp]
theorem internalMean_zeroMap :
    internalMean (zeroMap : InternalMap U X fun _ ↦ ℝ) = 0 := by
  rw [zeroMap, internalMean_ofFun]
  simp

section Discrete

variable [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- **The mean of a step map**: the corresponding combination of contents.

Needs the finite discrete stage structure, through `internalMean_indicatorMap`; the
value-side `lift_stepMap` above does not. -/
theorem internalMean_stepMap (l : List (ℝ × InternalSet U X)) :
    internalMean (stepMap l)
      = (l.map fun p ↦ p.1 * (internalContent U p.2).toReal).sum := by
  induction l with
  | nil => simp
  | cons p t ih =>
    rw [stepMap_cons,
      internalMean_add ((InternalSet.isUniformlyBounded_indicatorMap p.2).constMul p.1)
        (isUniformlyBounded_stepMap t), internalMean_constMul p.1
      (InternalSet.isUniformlyBounded_indicatorMap p.2), internalMean_indicatorMap, ih]
    simp

/-- **The integral identity for step maps** — the base case of the general theorem.

Assembled from F3a's two indicator calculations together with the linearity laws on both
sides: F1b's for the lifted function, F3a's for the mean. -/
theorem integral_lift_stepMap (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (l : List (ℝ × InternalSet U X)) :
    ∫ x, lift (stepMap l) x ∂(loebMeasure hU hX) = internalMean (stepMap l) := by
  induction l with
  | nil => simp
  | cons p t ih =>
    have hb := (InternalSet.isUniformlyBounded_indicatorMap p.2).constMul p.1
    have ht := isUniformlyBounded_stepMap (U := U) (X := X) t
    have hfun : (fun x ↦ lift (stepMap (p :: t)) x)
        = fun x ↦ p.1 * lift (InternalSet.indicatorMap p.2) x + lift (stepMap t) x := by
      funext x
      rw [stepMap_cons, lift_add hb ht,
        lift_constMul p.1 (InternalSet.isUniformlyBounded_indicatorMap p.2)]
    rw [hfun, integral_add (((integrable_lift hU hX
      (InternalSet.isUniformlyBounded_indicatorMap p.2)).const_mul p.1))
      (integrable_lift hU hX ht), integral_const_mul,
      InternalMap.integral_lift_indicatorMap, ih, stepMap_cons,
      internalMean_add hb ht,
      internalMean_constMul p.1 (InternalSet.isUniformlyBounded_indicatorMap p.2),
      internalMean_indicatorMap]

end Discrete

end Stage

/-! ### API tests -/

section Tests

/-- **The codebook shape F3b-ii will use**: coefficients indexed by a finite range of
integers, obtained from `Finset.toList`, with the stagewise sets given by a stagewise
predicate.

This is the smoke test that the `List` representation composes with `Finset.Icc`, which is
where the quantizer's stage-independent index set comes from. -/
example (a b : ℤ) (ε : ℝ) (A : ℤ → (i : ι) → Set (X i)) :
    stepMap ((Finset.Icc a b).toList.map fun k : ℤ ↦
        ((k : ℝ) * ε, (Filter.Product.ofFun (A k) : InternalSet U X)))
      = Filter.Product.ofFun fun i y ↦
          ((Finset.Icc a b).toList.map fun k : ℤ ↦
            (k : ℝ) * ε * Set.indicator (A k i) (fun _ ↦ (1 : ℝ)) y).sum := by
  -- Instantiated explicitly rather than left to `simp`: see the note on
  -- `stepMap_ofFun`'s `@[simp]` attribute.
  have h := stepMap_ofFun (U := U) ((Finset.Icc a b).toList.map fun k : ℤ ↦ ((k : ℝ) * ε, A k))
  simpa [List.map_map, Function.comp_def, mul_assoc] using h

/-- The codebook may repeat an entry; contributions add rather than collapse, which is why
it is a list and not a set. -/
example (c : ℝ) (A : InternalSet U X) (x : Ultraproduct U X) :
    lift (stepMap [(c, A), (c, A)]) x = 2 * lift (stepMap [(c, A)]) x := by
  rw [lift_stepMap, lift_stepMap]
  simp
  ring

end Tests

end InternalMap

end Loeb
