/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.Function
import LoebMeasure.Ultralimit.BoundedReal

/-!
# Bounded internal functions

A real-valued internal map, together with the property of being uniformly bounded, and the
pointwise function on the ultraproduct it lifts to.

## Boundedness is a property, not data

`BoundedInternalFunction` is a **subtype** of `InternalMap` over a `Prop`. The same
internal map equipped with two different bounds is therefore the same object, by
`Subtype.ext`. A structure carrying a `bound : ℝ` field — the shape the blueprint once
sketched — would distinguish them, which is wrong: a bound is a fact about a function, not
part of what the function *is*.

## The lift is total; boundedness is what makes it a limit

`InternalMap.lift` is defined on **all** real-valued internal maps, not on the subtype. It
descends the real ultrapower `InternalMap.toFun f x` through `Ultrafilter.ultralimit`,
which is itself total — junk where no limit exists, exactly as `Filter.lim` is.

So boundedness is not what makes the lift *definable*; it is what makes the lift a genuine
limit. That division is visible in the API, at two levels of the quotient:

* `lift_ofFun` is a total computation rule taking no boundedness hypothesis at all;
* the **representative-level** results `tendsto_lift_ofFun` and `norm_lift_ofFun_le` take
  an explicit eventual bound `∀ᶠ i in U, ∀ y, ‖g i y‖ ≤ C`, since a named bound is what
  their conclusions mention;
* only the **quotient-level** `exists_forall_norm_lift_le` takes `IsUniformlyBounded`
  itself, which is where the bound must be existentially quantified.

## One quotient, not two

The lift descends only the result of `InternalMap.toFun`, which already performs the
quotient-safe pointwise application (I4). A nested `liftOn` over both the function and the
point would work, but it would rebuild that abstraction and carry a second
well-definedness obligation for nothing. The scalar descent is inlined rather than given a
name, pending a second consumer.

## Hypotheses

No *additional* ones: no Loeb measure, no countable incompleteness, no stage finiteness,
nonemptiness, or measurability. This layer is quotient-level and analytic, and the measure
enters at F2.

The `Ultrafilter` structure on `U` is load-bearing, though, and not merely inherited
notation: F0's convergence theorem obtains a limit from a cluster point of the
pushed-forward *ultra*filter, so `tendsto_lift_ofFun` would fail for a general filter.

## Scope

The representation, the lift, and what boundedness buys about it — F1a.

Characteristic functions and cheap algebraic closure (negation, sums) are **F1b**, kept
separate rather than folded in here or deferred into F2: both are measure-free bridges
that belong before measurability, and the characteristic-function construction is what
should decide whether a bundled `ofFun`-style constructor improves the API. Adding one
speculatively now would prejudge that.

Measurability against `loebMeasurableSpace` is F2 and the integral identity is F3. No
normed-space instance is built here, since nothing yet asks for one.
-/

namespace Loeb

open Filter Topology

variable {ι : Type*} {U : Ultrafilter ι} {X : ι → Type*}

namespace InternalMap

/-- **Uniform boundedness of a real-valued internal map.**

Quotient-invariant: representatives agreeing eventually satisfy the same bounds, which is
the whole well-definedness obligation. Stated by `Filter.Product.liftOn` rather than as an
existential over representatives — the two are equivalent
(`isUniformlyBounded_iff_exists_ofFun`), and this form has a definitional computation rule.

The bound is a plain `ℝ` rather than an `ℝ≥0`. Since norms are nonnegative the two are
equivalent, and `ℝ` avoids coercions at every use. -/
def IsUniformlyBounded (f : InternalMap U X fun _ ↦ ℝ) : Prop :=
  Filter.Product.liftOn f (fun f' ↦ ∃ C : ℝ, ∀ᶠ i in (U : Filter ι), ∀ x, ‖f' i x‖ ≤ C)
    (fun _ _ h ↦ propext ⟨
      fun ⟨C, hC⟩ ↦ ⟨C, by
        filter_upwards [hC, h] with i hi hab x
        rw [← congrFun hab x]
        exact hi x⟩,
      fun ⟨C, hC⟩ ↦ ⟨C, by
        filter_upwards [hC, h] with i hi hab x
        rw [congrFun hab x]
        exact hi x⟩⟩)

/-- **The computation rule**, and it is definitional. -/
@[simp]
theorem isUniformlyBounded_ofFun (g : (i : ι) → X i → ℝ) :
    IsUniformlyBounded (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ) ↔
      ∃ C : ℝ, ∀ᶠ i in (U : Filter ι), ∀ x, ‖g i x‖ ≤ C :=
  Iff.rfl

/-- The existential-over-representatives formulation is equivalent.

Recorded because it is the shape one first reaches for, and because knowing the two agree
means the choice above was ergonomic rather than mathematical. -/
theorem isUniformlyBounded_iff_exists_ofFun (f : InternalMap U X fun _ ↦ ℝ) :
    IsUniformlyBounded f ↔
      ∃ (C : ℝ) (g : (i : ι) → X i → ℝ),
        f = Filter.Product.ofFun g ∧ ∀ᶠ i in (U : Filter ι), ∀ x, ‖g i x‖ ≤ C := by
  induction f using Filter.Product.inductionOn with
  | _ g =>
    rw [isUniformlyBounded_ofFun]
    refine ⟨fun ⟨C, hC⟩ ↦ ⟨C, g, rfl, hC⟩, ?_⟩
    rintro ⟨C, g', heq, hC⟩
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.Product.ofFun_eq_ofFun.1 heq] with i hi hgi x
    rw [congrFun hgi x]
    exact hi x

/-! ### The lift -/

/-- **The pointwise function on the ultraproduct** that a real-valued internal map lifts
to: the ultralimit of its stagewise evaluations.

Total, with no boundedness hypothesis — see the module docstring. It descends only the
real ultrapower `toFun f x`, so there is a single well-definedness obligation and it is
`Ultrafilter.ultralimit_congr`. -/
noncomputable def lift (f : InternalMap U X fun _ ↦ ℝ) (x : Ultraproduct U X) : ℝ :=
  Filter.Product.liftOn (toFun f x) (fun g ↦ U.ultralimit g)
    (fun _ _ h ↦ Ultrafilter.ultralimit_congr h)

/-- **The computation rule for the lift**, definitional and hypothesis-free. -/
@[simp]
theorem lift_ofFun (g : (i : ι) → X i → ℝ) (x : (i : ι) → X i) :
    lift (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
        (Filter.Product.ofFun x : Ultraproduct U X)
      = U.ultralimit fun i ↦ g i (x i) :=
  rfl

/-! ### What boundedness buys

Everything below takes `IsUniformlyBounded`. The rules above do not, which is the point:
the lift exists regardless, and boundedness is what makes it behave. -/

/-- **The lift is a genuine limit.** This is F0's `tendsto_ultralimit_of_eventually_norm_le`
reaching the function layer, and it is the reason `ℝ`'s non-compactness is not an
obstacle. -/
theorem tendsto_lift_ofFun {g : (i : ι) → X i → ℝ} {C : ℝ}
    (hC : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C) (x : (i : ι) → X i) :
    Tendsto (fun i ↦ g i (x i)) (U : Filter ι)
      (𝓝 (lift (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
        (Filter.Product.ofFun x))) := by
  rw [lift_ofFun]
  exact Ultrafilter.tendsto_ultralimit_of_eventually_norm_le (hC.mono fun i hi ↦ hi (x i))

/-- **A stagewise bound passes to the lift, uniformly in the point.** -/
theorem norm_lift_ofFun_le {g : (i : ι) → X i → ℝ} {C : ℝ}
    (hC : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C) (x : Ultraproduct U X) :
    ‖lift (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ) x‖ ≤ C := by
  induction x using Filter.Product.inductionOn with
  | _ x' =>
    rw [lift_ofFun]
    exact Ultrafilter.norm_ultralimit_le (hC.mono fun i hi ↦ hi (x' i))

/-- **A uniformly bounded internal map has a uniformly bounded lift**, with the same
bound. The quotient-level form of the previous statement. -/
theorem exists_forall_norm_lift_le {f : InternalMap U X fun _ ↦ ℝ}
    (hf : IsUniformlyBounded f) : ∃ C : ℝ, ∀ x, ‖lift f x‖ ≤ C := by
  induction f using Filter.Product.inductionOn with
  | _ g =>
    obtain ⟨C, hC⟩ := (isUniformlyBounded_ofFun g).1 hf
    exact ⟨C, norm_lift_ofFun_le hC⟩

end InternalMap

/-! ### The bundled type -/

/-- **A bounded internal function**: a real-valued internal map that is uniformly bounded.

A subtype over a `Prop`, so the bound is not part of the data and two bounded functions
with the same underlying map are equal. -/
def BoundedInternalFunction (U : Ultrafilter ι) (X : ι → Type*) :=
  {f : InternalMap U X fun _ ↦ ℝ // f.IsUniformlyBounded}

namespace BoundedInternalFunction

/-- The underlying internal map. -/
def toInternalMap (f : BoundedInternalFunction U X) : InternalMap U X fun _ ↦ ℝ := f.1

/-- The boundedness proof a bounded internal function carries. Named so callers need not
project through `Subtype.val`, and so that the `Prop`-valued nature of the field is legible
at the use site. -/
theorem isUniformlyBounded (f : BoundedInternalFunction U X) :
    f.toInternalMap.IsUniformlyBounded := f.2

/-- **Boundedness is proof-valued.** Two bounded internal functions with the same
underlying map are equal, whatever bounds witnessed them — the commitment a `bound : ℝ`
field would have broken. -/
@[ext]
theorem ext {f g : BoundedInternalFunction U X}
    (h : f.toInternalMap = g.toInternalMap) : f = g :=
  Subtype.ext h

/-- The pointwise function on the ultraproduct. -/
noncomputable def lift (f : BoundedInternalFunction U X) : Ultraproduct U X → ℝ :=
  f.toInternalMap.lift

/-- **A bounded internal function has a uniformly bounded lift.** The bundled form of
`InternalMap.exists_forall_norm_lift_le`; the bound is existential here because the type
carries the boundedness as a `Prop` rather than as data. -/
theorem exists_forall_norm_lift_le (f : BoundedInternalFunction U X) :
    ∃ C : ℝ, ∀ x, ‖f.lift x‖ ≤ C :=
  InternalMap.exists_forall_norm_lift_le f.2

end BoundedInternalFunction

/-! ### API tests -/

section Tests

/-- The boundedness rule is definitional. -/
example (g : (i : ι) → X i → ℝ) {C : ℝ}
    (h : ∀ᶠ i in (U : Filter ι), ∀ x, ‖g i x‖ ≤ C) :
    InternalMap.IsUniformlyBounded (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ) :=
  ⟨C, h⟩

/-- **The lift needs no boundedness.** It is defined for every real-valued internal map —
this statement elaborates with no hypothesis in sight — which is what lets the computation
rule be hypothesis-free. -/
example (g : (i : ι) → X i → ℝ) (x : (i : ι) → X i) :
    InternalMap.lift (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
        (Filter.Product.ofFun x)
      = U.ultralimit fun i ↦ g i (x i) :=
  rfl

/-- **Boundedness is what makes it a limit**, though — the division the module describes. -/
example {g : (i : ι) → X i → ℝ} {C : ℝ}
    (hC : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C) (x : (i : ι) → X i) :
    Tendsto (fun i ↦ g i (x i)) (U : Filter ι)
      (𝓝 (InternalMap.lift (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
        (Filter.Product.ofFun x))) :=
  InternalMap.tendsto_lift_ofFun hC x

/-- **The identity commitment, compiled**: same underlying map, same bounded function. -/
example (f g : BoundedInternalFunction U X) (h : f.toInternalMap = g.toInternalMap) :
    f = g :=
  BoundedInternalFunction.ext h

/-- And concretely: one map, two different bounds witnessing it, one object. -/
example (g : (i : ι) → X i → ℝ)
    (h₁ : InternalMap.IsUniformlyBounded (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ))
    (h₂ : InternalMap.IsUniformlyBounded (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)) :
    (⟨_, h₁⟩ : BoundedInternalFunction U X) = ⟨_, h₂⟩ :=
  BoundedInternalFunction.ext rfl

/-- **The bound is eventual, not pointwise** — inherited from F0, and necessary because
representatives may be wild off a large set. -/
example (g : (i : ι) → X i → ℝ) {s : Set ι} (hs : s ∈ U)
    (h : ∀ i ∈ s, ∀ x, ‖g i x‖ ≤ 1) :
    InternalMap.IsUniformlyBounded (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ) :=
  ⟨1, Filter.eventually_of_mem hs h⟩

/-- **A genuinely dependent family** of stage types. -/
example (U : Ultrafilter ℕ) (g : (i : ℕ) → Fin (i + 1) → ℝ)
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ x, ‖g i x‖ ≤ 1) (x : (i : ℕ) → Fin (i + 1)) :
    ‖InternalMap.lift (Filter.Product.ofFun g : InternalMap U (fun i ↦ Fin (i + 1)) fun _ ↦ ℝ)
      (Filter.Product.ofFun x)‖ ≤ 1 :=
  InternalMap.norm_lift_ofFun_le h _

end Tests

end Loeb
