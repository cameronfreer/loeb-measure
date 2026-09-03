/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Integral.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integration primitives for bounded internal functions

The stagewise-average functional, integrability of the lift, and the indicator calculation
— the setup F3b's approximation argument consumes.

## What is here and what is not

The integral identity itself is **F3b**. This module deliberately contains no quantizer and
no approximation proof: those carry all the risk, and keeping them out leaves this API
stable and independently reviewable.

## `internalMean` is total, like `lift`

`InternalMap.internalMean` is defined on **all** real-valued internal maps, not on the
bounded subtype, matching F1a's convention for `lift`. It descends a single quotient
through `Ultrafilter.ultralimit`, which is itself total, so boundedness is not what makes
it definable — only what makes it behave. It takes neither `hU` nor `hX`.

## Linearity on the two sides is *not* the same fact

F1b's `lift_add` and `lift_constMul` give linearity of the *lifted function*, and hence of
the left-hand side of the eventual identity. They say nothing about `internalMean`. That
side needs finite-stage integral linearity together with F0's bounded-real ultralimit
arithmetic, which is what `internalMean_add` and `internalMean_constMul` below supply. The
two are proved separately because they are separate facts.

## Where the Loeb measure enters, and the `ℝ≥0∞` boundary

`loebMeasure` and `hU` appear here for the first time in M5 — F1 and F2 have neither — and
only in the statements that mention the Loeb integral. `internalMean` is **Loeb-measure-free**,
not measure-free: it is built from the stage measures `normalizedCounting`, and only the
Loeb measure is absent from it.

Conversions from `ℝ≥0∞` to `ℝ` are unavoidable at this layer, since `internalContent` and
`loebMeasure` are `ℝ≥0∞`-valued while `∫` is real. What is confined is the conversion of the
**Loeb measure and the internal content**, which happens in `integral_lift_indicatorMap`
and `internalMean_indicatorMap` and goes through `MeasureTheory.Measure.real` and
`ENNReal.toReal`. No parallel real-valued content is introduced: the project has one
content, in `ℝ≥0∞`.

## Hypotheses

`internalMean`, its computation rule, the algebraic laws and the indicator mean: no `hU`,
no `hX`. Integrable and Loeb-integral statements: both, and `hU` only through
`loebMeasure`. Nothing here imports saturation or the M3 approximation layer.

`norm_internalMean_le` does take `0 ≤ C`, and genuinely: on an empty stage the bound
hypothesis is vacuous while the stage integral is `0`, so a negative bound would be
contradicted.
-/

namespace Loeb

open Filter MeasureTheory Topology

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] {U : Ultrafilter ι}

namespace InternalMap

/-! ### The stagewise mean -/

/-- **The stagewise average of an internal map**: the ultralimit of its stagewise integrals
against the normalized counting measures.

Total, like `lift`, and for the same reason — `Ultrafilter.ultralimit` is total, so
boundedness is what makes this a genuine limit rather than what makes it definable. The
well-definedness obligation is `ultralimit_congr` on eventually equal representatives. -/
noncomputable def internalMean (f : InternalMap U X fun _ ↦ ℝ) : ℝ :=
  Filter.Product.liftOn f
    (fun g ↦ U.ultralimit fun i ↦ ∫ y, g i y ∂normalizedCounting (X i))
    (fun _ _ h ↦ Ultrafilter.ultralimit_congr (h.mono fun _ hi ↦ by simp only [hi]))

omit [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
/-- **The computation rule**, definitional. -/
@[simp]
theorem internalMean_ofFun (g : (i : ι) → X i → ℝ) :
    internalMean (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
      = U.ultralimit fun i ↦ ∫ y, g i y ∂normalizedCounting (X i) :=
  rfl

omit [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
/-- A stagewise bound bounds each stage integral, since the stage measures have mass at
most one. The step `internalMean`'s own bound and its arithmetic laws both rest on. -/
theorem norm_integral_normalizedCounting_le {g : (i : ι) → X i → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (i : ι) (h : ∀ y, ‖g i y‖ ≤ C) :
    ‖∫ y, g i y ∂normalizedCounting (X i)‖ ≤ C := by
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ h)).trans ?_
  have hle : (normalizedCounting (X i)).real Set.univ ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using normalizedCounting_le_one (X := X i) Set.univ)
  nlinarith [hle, measureReal_nonneg (μ := normalizedCounting (X i)) (s := Set.univ)]

omit [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
/-- **A uniformly bounded internal map has a bounded mean**, with the same bound. -/
theorem norm_internalMean_le {g : (i : ι) → X i → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C) :
    ‖internalMean (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)‖ ≤ C := by
  rw [internalMean_ofFun]
  exact Ultrafilter.norm_ultralimit_le
    (h.mono fun i hi ↦ norm_integral_normalizedCounting_le hC i hi)

/-! ### Arithmetic of the mean

**A separate fact from F1b's arithmetic**, which concerns the lifted function. These
concern the ultralimit of stage integrals, and need finite-stage integral linearity
together with F0's bounded-real ultralimit rules. F3b consumes both sides. -/

/-- **The mean is additive**, given bounds. -/
theorem internalMean_add_ofFun {g h : (i : ι) → X i → ℝ} {C D : ℝ}
    (hg : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C)
    (hh : ∀ᶠ i in (U : Filter ι), ∀ y, ‖h i y‖ ≤ D) :
    internalMean (add (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
        (Filter.Product.ofFun h))
      = internalMean (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
        + internalMean (Filter.Product.ofFun h : InternalMap U X fun _ ↦ ℝ) := by
  rw [add_ofFun, internalMean_ofFun, internalMean_ofFun, internalMean_ofFun,
    ← Ultrafilter.ultralimit_add_of_eventually_norm_le (C := |C|) (D := |D|)
      (hg.mono fun i hi ↦ norm_integral_normalizedCounting_le (abs_nonneg C) i
        fun y ↦ (hi y).trans (le_abs_self C))
      (hh.mono fun i hi ↦ norm_integral_normalizedCounting_le (abs_nonneg D) i
        fun y ↦ (hi y).trans (le_abs_self D))]
  refine Ultrafilter.ultralimit_congr (Eventually.of_forall fun i ↦ ?_)
  -- The stages are finite, so every stagewise function is integrable outright.
  exact integral_add (Integrable.of_finite) (Integrable.of_finite)

omit [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
/-- **The mean commutes with scaling.**

A bound is still required, as for additivity — F0's scalar rule needs one. What needs no
side condition is the **scalar** `c` itself, unlike the `ℝ≥0∞` form which requires
`c ≠ ∞`, because real multiplication is continuous everywhere. -/
theorem internalMean_constMul_ofFun {g : (i : ι) → X i → ℝ} {C : ℝ} (c : ℝ)
    (hg : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C) :
    internalMean (constMul c (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ))
      = c * internalMean (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ) := by
  rw [constMul_ofFun, internalMean_ofFun, internalMean_ofFun,
    ← Ultrafilter.ultralimit_const_mul_of_eventually_norm_le (c := c) (C := |C|)
      (hg.mono fun i hi ↦ norm_integral_normalizedCounting_le (abs_nonneg C) i
        (fun y ↦ (hi y).trans (le_abs_self C)))]
  exact Ultrafilter.ultralimit_congr
    (Eventually.of_forall fun i ↦ integral_const_mul c (g i))

/-- **The mean of an indicator is the content**, converted to a real.

The right-hand counterpart of `integral_lift_indicatorMap`, and **Loeb-measure-free**: it
takes neither `hU` nor `hX`, so F3b gets both sides of the indicator calculation without
developing this one itself.

The conversion goes through the ultralimit rather than around it: the stagewise values are
`(normalizedCounting (X i)).real (A i)`, whose ultralimit is the `toReal` of the content
because the content is finite and `ENNReal.toReal` is continuous there. -/
theorem internalMean_indicatorMap (A : InternalSet U X) :
    internalMean (InternalSet.indicatorMap A) = (internalContent U A).toReal := by
  induction A using Filter.Product.inductionOn with
  | _ A' =>
    rw [InternalSet.indicatorMap_ofFun, internalMean_ofFun, internalContent_ofFun]
    have hstage : ∀ i, ∫ y, Set.indicator (A' i) (fun _ ↦ (1 : ℝ)) y
        ∂normalizedCounting (X i) = (normalizedCounting (X i) (A' i)).toReal := fun i ↦ by
      rw [show (fun _ ↦ (1 : ℝ)) = (1 : X i → ℝ) from rfl,
        integral_indicator_one (Set.toFinite (A' i)).measurableSet]
      rfl
    rw [Ultrafilter.ultralimit_congr (Eventually.of_forall hstage)]
    refine tendsto_nhds_unique
      (Ultrafilter.tendsto_ultralimit_of_eventually_norm_le (C := 1)
        (Eventually.of_forall fun i ↦ ?_)) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by simpa using normalizedCounting_le_one (X := X i) (A' i))
    · exact (ENNReal.tendsto_toReal
        (internalContent_ne_top (U := U) (Filter.Product.ofFun A'))).comp
          (Ultrafilter.tendsto_ultralimit U _)

/-! ### Quotient-level laws

The forms F3b and later layers should use: `IsUniformlyBounded` on arbitrary internal
maps, with no representative in sight. The `…_ofFun` rules above stay for proofs that
already hold a named bound. -/

/-- **The mean is additive**, at the quotient level. -/
theorem internalMean_add {f g : InternalMap U X fun _ ↦ ℝ} (hf : f.IsUniformlyBounded)
    (hg : g.IsUniformlyBounded) :
    internalMean (add f g) = internalMean f + internalMean g := by
  induction f, g using Filter.Product.inductionOn₂ with
  | _ f' g' =>
    obtain ⟨C, hC⟩ := (isUniformlyBounded_ofFun f').1 hf
    obtain ⟨D, hD⟩ := (isUniformlyBounded_ofFun g').1 hg
    exact internalMean_add_ofFun hC hD

omit [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
/-- **The mean commutes with scaling**, at the quotient level. -/
theorem internalMean_constMul {f : InternalMap U X fun _ ↦ ℝ} (c : ℝ)
    (hf : f.IsUniformlyBounded) :
    internalMean (constMul c f) = c * internalMean f := by
  induction f using Filter.Product.inductionOn with
  | _ g =>
    obtain ⟨C, hC⟩ := (isUniformlyBounded_ofFun g).1 hf
    exact internalMean_constMul_ofFun c hC

/-! ### The Loeb measure enters -/

/-- **The lift of a uniformly bounded internal map is integrable.**

Measurable by F2, bounded by F1a, and `loebMeasure` is a probability measure — so the
constant bound is integrable and dominates. -/
theorem integrable_lift (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) {f : InternalMap U X fun _ ↦ ℝ}
    (hf : f.IsUniformlyBounded) :
    Integrable (lift f) (loebMeasure hU hX) := by
  obtain ⟨C, hC⟩ := exists_forall_norm_lift_le hf
  exact (integrable_const C).mono'
    ((measurable_lift hX hf).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ hC x)

/-- **The indicator calculation.** The Loeb integral of a realized internal set's
characteristic function is that set's content, converted to a real.

Composes F1b's set bridge with M3's `loebMeasure_internal`. The `ℝ≥0∞`-to-`ℝ` conversion is
confined here and goes through `MeasureTheory.Measure.real`; the project keeps one content,
in `ℝ≥0∞`. -/
theorem integral_lift_indicatorMap (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (A : InternalSet U X) :
    ∫ x, lift (InternalSet.indicatorMap A) x ∂(loebMeasure hU hX)
      = (internalContent U A).toReal := by
  have hfun : lift (InternalSet.indicatorMap A)
      = Set.indicator (InternalSet.carrier A) (1 : Ultraproduct U X → ℝ) := by
    funext x
    exact InternalSet.lift_indicatorMap A x
  rw [hfun, integral_indicator_one (measurableSet_internal hX A), Measure.real,
    loebMeasure_internal]

end InternalMap

/-! ### Bundled wrappers -/

namespace BoundedInternalFunction

/-- The stagewise mean of a bounded internal function. -/
noncomputable def internalMean (f : BoundedInternalFunction U X) : ℝ :=
  f.toInternalMap.internalMean

/-- The lift of a bounded internal function is integrable. -/
theorem integrable_lift (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (f : BoundedInternalFunction U X) :
    Integrable f.lift (loebMeasure hU hX) :=
  InternalMap.integrable_lift hU hX f.2

/-- The indicator calculation, bundled. -/
theorem integral_lift_indicator (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (A : InternalSet U X) :
    ∫ x, (BoundedInternalFunction.indicator A).lift x ∂(loebMeasure hU hX)
      = (internalContent U A).toReal :=
  InternalMap.integral_lift_indicatorMap hU hX A

end BoundedInternalFunction

/-! ### API tests -/

section Tests

/-- `internalMean` is measure-free: this statement mentions neither `hU` nor `hX`. -/
example (g : (i : ι) → X i → ℝ) :
    InternalMap.internalMean (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
      = U.ultralimit fun i ↦ ∫ y, g i y ∂normalizedCounting (X i) :=
  rfl

/-- **The indicator calculation**, which is E5's characteristic-function commitment at the
integral level — the third rung after values (F1b) and measurability (F2). -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (A : InternalSet U X) :
    ∫ x, InternalMap.lift (InternalSet.indicatorMap A) x ∂(loebMeasure hU hX)
      = (internalContent U A).toReal :=
  InternalMap.integral_lift_indicatorMap hU hX A

/-- Integrability, at the quotient level. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    {f : InternalMap U X fun _ ↦ ℝ} (hf : f.IsUniformlyBounded) :
    Integrable (InternalMap.lift f) (loebMeasure hU hX) :=
  InternalMap.integrable_lift hU hX hf

/-- **The two linearities are different facts.** F1b's law is about the lifted function;
this one is about the ultralimit of stage integrals. Both are needed by F3b, and neither
implies the other. -/
example {f g : InternalMap U X fun _ ↦ ℝ} (hf : f.IsUniformlyBounded)
    (hg : g.IsUniformlyBounded) :
    InternalMap.internalMean (InternalMap.add f g)
      = InternalMap.internalMean f + InternalMap.internalMean g :=
  InternalMap.internalMean_add hf hg

/-- **Both indicator calculations**, the Loeb-integral side and the mean side. F3b consumes
the pair; neither has to be developed there. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (A : InternalSet U X) :
    ∫ x, InternalMap.lift (InternalSet.indicatorMap A) x ∂(loebMeasure hU hX)
      = InternalMap.internalMean (InternalSet.indicatorMap A) := by
  rw [InternalMap.integral_lift_indicatorMap, InternalMap.internalMean_indicatorMap]

/-- **The mean side needs no Loeb-measure hypotheses** — neither `hU` nor `hX` appears. -/
example (A : InternalSet U X) :
    InternalMap.internalMean (InternalSet.indicatorMap A) = (internalContent U A).toReal :=
  InternalMap.internalMean_indicatorMap A

/-- Scaling, at the quotient level. -/
example {f : InternalMap U X fun _ ↦ ℝ} (c : ℝ) (hf : f.IsUniformlyBounded) :
    InternalMap.internalMean (InternalMap.constMul c f)
      = c * InternalMap.internalMean f :=
  InternalMap.internalMean_constMul c hf

/-- The mean is bounded by any stagewise bound. -/
example {g : (i : ι) → X i → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C) :
    ‖InternalMap.internalMean (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)‖ ≤ C :=
  InternalMap.norm_internalMean_le hC h

/-- **A genuinely dependent family** of stage types. -/
example (U : Ultrafilter ℕ) (g : (i : ℕ) → Fin (i + 1) → ℝ) :
    InternalMap.internalMean
        (Filter.Product.ofFun g : InternalMap U (fun i ↦ Fin (i + 1)) fun _ ↦ ℝ)
      = U.ultralimit fun i ↦ ∫ y, g i y ∂normalizedCounting (Fin (i + 1)) :=
  rfl

end Tests

end Loeb
