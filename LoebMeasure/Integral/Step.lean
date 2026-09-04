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

The list is the **codebook**: a finite set of coefficients paired with internal sets, fixed
independently of the stage. That is what makes the approximation in
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

@[simp]
theorem lift_zeroMap (x : Ultraproduct U X) : lift (zeroMap : InternalMap U X fun _ ↦ ℝ) x = 0 := by
  induction x using Filter.Product.inductionOn with
  | _ x' => simp [zeroMap]

theorem isUniformlyBounded_zeroMap :
    (zeroMap : InternalMap U X fun _ ↦ ℝ).IsUniformlyBounded :=
  ⟨0, Eventually.of_forall fun _ _ ↦ by simp⟩

/-- **A finite linear combination of internal indicators.**

The list is a codebook fixed independently of the stage. Built by recursion from `add`,
`constMul` and `indicatorMap` rather than through an algebraic instance. -/
noncomputable def stepMap : List (ℝ × InternalSet U X) → InternalMap U X fun _ ↦ ℝ
  | [] => zeroMap
  | p :: t => add (constMul p.1 (InternalSet.indicatorMap p.2)) (stepMap t)

@[simp]
theorem stepMap_nil : stepMap ([] : List (ℝ × InternalSet U X)) = zeroMap := rfl

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

section Stage

variable [∀ i, MeasurableSpace (X i)]

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

end InternalMap

end Loeb
