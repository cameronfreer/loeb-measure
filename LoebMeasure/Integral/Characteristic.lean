/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Integral.Bounded
import LoebMeasure.Internal.BooleanAlgebra

/-!
# Characteristic functions and arithmetic of bounded internal functions

Two measure-free bridges between F1a's bounded internal functions and the layers on either
side: indicators connect them **down** to M2's internal sets, and negation and addition are
the closure facts F3's integral will need.

## The set bridge

E5 commits that characteristic functions recover the M3 set API. The statement that does
that is `lift_indicatorMap`:

```
InternalMap.lift (InternalSet.indicatorMap A) x
  = (InternalSet.carrier A).indicator (fun _ ↦ 1) x
```

It is not formal. The stagewise family is `{0, 1}`-valued, and deciding which value the
ultralimit takes is exactly the **ultrafilter dichotomy**: either the point is eventually
in the stagewise sets, and the family is eventually the constant `1`, or it is eventually
outside them and the family is eventually `0`. `Ultrafilter.eventually_not` is what splits
those cases, and a general filter admits neither.

That makes this the first place in Layer B where an ultrafilter property beyond F0's
convergence argument is consumed.

## Arithmetic needs boundedness

`lift_add` and `lift_neg` take boundedness, and not as bookkeeping: an ultralimit is
additive only when the summands converge, which on `ℝ` is what a bound supplies. The
`ℝ≥0∞` analogue `Loeb.ultralimit_add` is unconditional precisely because that space is
compact and every family converges.

## Hypotheses

No Loeb measure, no countable incompleteness, no stage finiteness, nonemptiness, or
measurability — F1b stays measure-free, which is why it lands before F2 rather than inside
it. What it does use, beyond F1a, is the ultrafilter dichotomy, in the indicator bridge
alone.

## On a bundled constructor

F1a deliberately left open whether `BoundedInternalFunction` wants an `ofFun`-style
constructor, with this unit's indicator construction as the test. The answer is **no**:
`BoundedInternalFunction.indicator` builds the bundled object directly from an internal set
in one line, and a generic constructor would not have shortened it. None is added.
-/

namespace Loeb

open Filter Topology

variable {ι : Type*} {U : Ultrafilter ι} {X : ι → Type*}

/-! ### Characteristic functions -/

namespace InternalSet

/-- **The characteristic function of an internal set**, as an internal map.

Built by `Filter.Product.map`, so no representative is chosen and there is no
well-definedness obligation. -/
noncomputable def indicatorMap (A : InternalSet U X) : InternalMap U X fun _ ↦ ℝ :=
  Filter.Product.map (fun _ s ↦ Set.indicator s fun _ ↦ (1 : ℝ)) A

@[simp]
theorem indicatorMap_ofFun (A : (i : ι) → Set (X i)) :
    indicatorMap (Filter.Product.ofFun A : InternalSet U X)
      = Filter.Product.ofFun fun i ↦ Set.indicator (A i) fun _ ↦ (1 : ℝ) :=
  Filter.Product.map_ofFun _ _

/-- Indicators are uniformly bounded by `1`, pointwise and hence eventually. -/
theorem isUniformlyBounded_indicatorMap (A : InternalSet U X) :
    (indicatorMap A).IsUniformlyBounded := by
  induction A using Filter.Product.inductionOn with
  | _ A' =>
    rw [indicatorMap_ofFun, InternalMap.isUniformlyBounded_ofFun]
    refine ⟨1, Eventually.of_forall fun i x ↦ ?_⟩
    by_cases hx : x ∈ A' i <;> simp [hx]

/-- **The set bridge**: the lift of an internal set's characteristic function is the
characteristic function of its realized carrier.

Where the ultrafilter dichotomy enters Layer B. The stagewise family takes only the values
`0` and `1`, and which one the ultralimit takes is decided by whether the point is
eventually inside the stagewise sets — a dichotomy no general filter provides. -/
@[simp]
theorem lift_indicatorMap (A : InternalSet U X) (x : Ultraproduct U X) :
    InternalMap.lift (indicatorMap A) x
      = Set.indicator (carrier A) (fun _ ↦ (1 : ℝ)) x := by
  induction A, x using Filter.Product.inductionOn₂ with
  | _ A' x' =>
    rw [indicatorMap_ofFun, InternalMap.lift_ofFun]
    by_cases hmem : ∀ᶠ i in (U : Filter ι), x' i ∈ A' i
    · rw [Ultrafilter.ultralimit_congr (g := fun _ ↦ (1 : ℝ))
        (hmem.mono fun i hi ↦ by simp [Set.indicator_of_mem hi]),
        Ultrafilter.ultralimit_const,
        Set.indicator_of_mem ((mem_carrier_ofFun x' A').2 hmem)]
    · rw [Ultrafilter.ultralimit_congr (g := fun _ ↦ (0 : ℝ))
        ((Ultrafilter.eventually_not.2 hmem).mono fun i hi ↦ by
          simp [Set.indicator_of_notMem hi]),
        Ultrafilter.ultralimit_const,
        Set.indicator_of_notMem fun h ↦ hmem ((mem_carrier_ofFun x' A').1 h)]

end InternalSet

/-- **The bundled characteristic function** of an internal set.

Built directly, in one line. This is the construction F1a reserved as the test of whether a
generic `ofFun`-style constructor for `BoundedInternalFunction` would help; it would not,
so none exists. -/
noncomputable def BoundedInternalFunction.indicator (A : InternalSet U X) :
    BoundedInternalFunction U X :=
  ⟨InternalSet.indicatorMap A, InternalSet.isUniformlyBounded_indicatorMap A⟩

@[simp]
theorem BoundedInternalFunction.lift_indicator (A : InternalSet U X) (x : Ultraproduct U X) :
    (BoundedInternalFunction.indicator A).lift x
      = Set.indicator (InternalSet.carrier A) (fun _ ↦ (1 : ℝ)) x :=
  InternalSet.lift_indicatorMap A x

/-! ### Arithmetic

Closure facts, with the lift commuting. Every statement about the *lift* takes boundedness;
the closure statements take it too, since that is what they are about. -/

namespace InternalMap

/-- Negation of an internal map, stagewise. -/
def neg (f : InternalMap U X fun _ ↦ ℝ) : InternalMap U X fun _ ↦ ℝ :=
  Filter.Product.map (fun _ g ↦ -g) f

/-- Addition of internal maps, stagewise. -/
def add (f g : InternalMap U X fun _ ↦ ℝ) : InternalMap U X fun _ ↦ ℝ :=
  Filter.Product.map₂ (fun _ a b ↦ a + b) f g

@[simp]
theorem neg_ofFun (g : (i : ι) → X i → ℝ) :
    neg (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
      = Filter.Product.ofFun fun i ↦ -g i :=
  Filter.Product.map_ofFun _ _

@[simp]
theorem add_ofFun (g h : (i : ι) → X i → ℝ) :
    add (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ) (Filter.Product.ofFun h)
      = Filter.Product.ofFun fun i ↦ g i + h i :=
  Filter.Product.map₂_ofFun _ _ _

theorem IsUniformlyBounded.neg {f : InternalMap U X fun _ ↦ ℝ}
    (hf : f.IsUniformlyBounded) : (neg f).IsUniformlyBounded := by
  induction f using Filter.Product.inductionOn with
  | _ g =>
    obtain ⟨C, hC⟩ := (isUniformlyBounded_ofFun g).1 hf
    rw [neg_ofFun, isUniformlyBounded_ofFun]
    exact ⟨C, hC.mono fun i hi x ↦ by simpa using hi x⟩

theorem IsUniformlyBounded.add {f g : InternalMap U X fun _ ↦ ℝ}
    (hf : f.IsUniformlyBounded) (hg : g.IsUniformlyBounded) :
    (add f g).IsUniformlyBounded := by
  induction f, g using Filter.Product.inductionOn₂ with
  | _ f' g' =>
    obtain ⟨C, hC⟩ := (isUniformlyBounded_ofFun f').1 hf
    obtain ⟨D, hD⟩ := (isUniformlyBounded_ofFun g').1 hg
    rw [add_ofFun, isUniformlyBounded_ofFun]
    refine ⟨C + D, ?_⟩
    filter_upwards [hC, hD] with i hi hi' x
    exact (norm_add_le _ _).trans (add_le_add (hi x) (hi' x))

/-- **The lift commutes with negation**, given a bound. -/
theorem lift_neg_ofFun {g : (i : ι) → X i → ℝ} {C : ℝ}
    (hC : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C) (x : Ultraproduct U X) :
    lift (neg (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)) x
      = -lift (Filter.Product.ofFun g) x := by
  induction x using Filter.Product.inductionOn with
  | _ x' =>
    rw [neg_ofFun, lift_ofFun, lift_ofFun]
    exact Ultrafilter.ultralimit_neg_of_eventually_norm_le (hC.mono fun i hi ↦ hi (x' i))

/-- **The lift commutes with addition**, given bounds.

Boundedness is load-bearing rather than bookkeeping: an ultralimit is additive only when
the summands converge, which on `ℝ` is what a bound supplies. -/
theorem lift_add_ofFun {g h : (i : ι) → X i → ℝ} {C D : ℝ}
    (hC : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C)
    (hD : ∀ᶠ i in (U : Filter ι), ∀ y, ‖h i y‖ ≤ D) (x : Ultraproduct U X) :
    lift (add (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
        (Filter.Product.ofFun h)) x
      = lift (Filter.Product.ofFun g) x + lift (Filter.Product.ofFun h) x := by
  induction x using Filter.Product.inductionOn with
  | _ x' =>
    rw [add_ofFun, lift_ofFun, lift_ofFun, lift_ofFun]
    exact Ultrafilter.ultralimit_add_of_eventually_norm_le
      (hC.mono fun i hi ↦ hi (x' i)) (hD.mono fun i hi ↦ hi (x' i))

end InternalMap

/-! ### API tests -/

section Tests

/-- **The set bridge**, in the shape F3's integral will consume: the lift of an indicator
is the indicator of the carrier. -/
example (A : InternalSet U X) (x : Ultraproduct U X) :
    InternalMap.lift (InternalSet.indicatorMap A) x
      = Set.indicator (InternalSet.carrier A) (fun _ ↦ (1 : ℝ)) x := by
  simp

/-- **It takes the value `1` exactly on the carrier**, which is the M3 set API being
recovered rather than merely referenced. -/
example (A : InternalSet U X) (x : Ultraproduct U X) (hx : x ∈ InternalSet.carrier A) :
    InternalMap.lift (InternalSet.indicatorMap A) x = 1 := by
  rw [InternalSet.lift_indicatorMap, Set.indicator_of_mem hx]

/-- And `0` off it. -/
example (A : InternalSet U X) (x : Ultraproduct U X) (hx : x ∉ InternalSet.carrier A) :
    InternalMap.lift (InternalSet.indicatorMap A) x = 0 := by
  rw [InternalSet.lift_indicatorMap, Set.indicator_of_notMem hx]

/-- The bundled form, built in one line from an internal set. -/
example (A : InternalSet U X) (x : Ultraproduct U X) :
    (BoundedInternalFunction.indicator A).lift x
      = Set.indicator (InternalSet.carrier A) (fun _ ↦ (1 : ℝ)) x := by
  simp

/-- **The empty internal set gives the zero function**, through `carrier_bot` — a check
that the bridge composes with M2's carrier laws rather than living beside them. -/
example (x : Ultraproduct U X) :
    InternalMap.lift (InternalSet.indicatorMap (⊥ : InternalSet U X)) x = 0 := by
  rw [InternalSet.lift_indicatorMap, InternalSet.carrier_bot]
  simp

/-- **And the full internal set gives the constant one**, through `carrier_top`. -/
example (x : Ultraproduct U X) :
    InternalMap.lift (InternalSet.indicatorMap (⊤ : InternalSet U X)) x = 1 := by
  rw [InternalSet.lift_indicatorMap, InternalSet.carrier_top]
  simp

/-- Closure under addition, at the quotient level. -/
example {f g : InternalMap U X fun _ ↦ ℝ} (hf : f.IsUniformlyBounded)
    (hg : g.IsUniformlyBounded) : (InternalMap.add f g).IsUniformlyBounded :=
  hf.add hg

/-- The lift commutes with addition, given bounds. -/
example {g h : (i : ι) → X i → ℝ} {C D : ℝ}
    (hC : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C)
    (hD : ∀ᶠ i in (U : Filter ι), ∀ y, ‖h i y‖ ≤ D) (x : Ultraproduct U X) :
    InternalMap.lift (InternalMap.add (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
        (Filter.Product.ofFun h)) x
      = InternalMap.lift (Filter.Product.ofFun g) x
        + InternalMap.lift (Filter.Product.ofFun h) x :=
  InternalMap.lift_add_ofFun hC hD x

/-- **A genuinely dependent family.** -/
example (U : Ultrafilter ℕ) (A : InternalSet U fun i ↦ Fin (i + 1))
    (x : Ultraproduct U fun i ↦ Fin (i + 1)) :
    InternalMap.lift (InternalSet.indicatorMap A) x
      = Set.indicator (InternalSet.carrier A) (fun _ ↦ (1 : ℝ)) x :=
  InternalSet.lift_indicatorMap A x

end Tests

end Loeb
