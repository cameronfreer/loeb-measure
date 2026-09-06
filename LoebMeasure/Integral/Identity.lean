/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Integral.Step

/-!
# The integral identity

The Loeb integral of the lift of a uniformly bounded internal map is the ultralimit of its
stagewise averages:

```lean
∫ x, lift f x ∂(loebMeasure hU hX) = internalMean f
```

This closes E5. Every earlier unit of M5 was setup for it, and F3b-i's step maps are the
case the general statement is reduced to.

## The argument

Three inequalities and one identity. For `ε > 0`, a uniformly bounded `f` is within `ε` of
some step map `q` — **on both sides**: at every point of the lift and in the mean. The
integral identity holds for `q` outright (`integral_lift_stepMap`). Since the Loeb measure
is a probability measure, the Loeb integrals of `f` and `q` are within `ε` as well, and the
triangle inequality bounds the discrepancy of the two sides for `f` by `2ε`. As `ε` was
arbitrary, they agree.

A lift-only approximation would not do: it says nothing about `internalMean`, and the
identity has two sides. The approximation theorem therefore controls both.

## The quantizer

`InternalMap.quantizer ε C g` is a **single finite codebook, independent of the stage**:
its index set is `Finset.Icc ⌊-C / ε⌋ ⌊C / ε⌋`, which depends on the bound `C` and the mesh
`ε` and on nothing else, and its `k`-th entry pairs the level `k * ε` with the stagewise
level set `{y | ⌊g i y / ε⌋ = k}`. Those level sets are internal by construction, not by
an argument. At any stage where the bound holds, exactly one entry fires at each point, and
the step map takes the value `⌊g i y / ε⌋ * ε` there, within `ε` of `g i y`.

"Finite-valued" would have been vacuous as a criterion — each stage is finite already — and
"some internal map within `ε`" unusable, since the proof needs linearity and the indicator
calculation to apply. A step map with a stage-independent codebook is what both require.

The stagewise error is strict, `< ε`. After the ultralimit it is `≤ ε`, which is what the
quotient-level statements assert: limits do not preserve strictness.

## Hypotheses, layer by layer

* The quantizer, `stepMap_quantizer` and the representative-level approximation theorem
  take **no stage instances at all** — not even `MeasurableSpace` — and neither `hU` nor
  `hX`.
* The quotient-level approximation controls `internalMean` too, so it needs the finite
  discrete stage structure, through F3a's mean laws. Still no `hU`, no `hX`.
* `integral_lift` and its corollaries mention `loebMeasure`, hence `hU` and `hX`, and
  countable incompleteness enters **only** through `loebMeasure`. No saturation, and nothing
  from the M3 approximation layer.
* The standalone finite-stage formula `integral_normalizedCounting` needs **no
  nonemptiness** and is exercised on `Empty`. The main theorem cannot cover empty stages,
  `hX` being part of the Loeb construction; that asymmetry is real and is stated rather
  than hidden.
-/

namespace Loeb

open Filter MeasureTheory Topology

variable {ι : Type*} {X : ι → Type*} {U : Ultrafilter ι}

/-! ### The finite-stage formula

Kept in the integral layer: `Measure/Counting.lean` has no Bochner dependency, and this is
the one place the normalized counting measure meets an integral. -/

section FiniteStage

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y] [MeasurableSingletonClass Y]

/-- **The integral against the normalized counting measure is the normalized sum.**

No nonemptiness: on an empty type both sides are `0`, the left because the measure is zero
and the right because the sum is empty. `Fintype` rather than `Finite`, since the right-hand
side is a `Finset.sum` over `univ`. -/
theorem integral_normalizedCounting (g : Y → ℝ) :
    ∫ y, g y ∂normalizedCounting Y = (1 / Fintype.card Y : ℝ) * ∑ y, g y := by
  rw [integral_fintype (hf := Integrable.of_finite), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Measure.real, normalizedCounting_singleton, smul_eq_mul, Nat.card_eq_fintype_card,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

end FiniteStage

namespace InternalMap

/-! ### The quantizer

No stage instances in this section: the codebook is a list of levels paired with internal
sets, and the error estimate is an inequality of reals at each stage. -/

/-- One mesh cell's worth of rounding error. `private`: a fact about reals, with no consumer
beyond the quantizer. -/
private theorem abs_sub_floor_div_mul_lt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    |t - ⌊t / ε⌋ * ε| < ε := by
  have h : t - ⌊t / ε⌋ * ε = Int.fract (t / ε) * ε := by
    rw [Int.fract, sub_mul, div_mul_cancel₀ t hε.ne']
  rw [h, abs_of_nonneg (mul_nonneg (Int.fract_nonneg _) hε.le)]
  calc Int.fract (t / ε) * ε < 1 * ε := by gcongr; exact Int.fract_lt_one _
    _ = ε := one_mul ε

/-- **The stage-independent codebook.** Levels `k * ε` for `k` in the integer range
`⌊-C / ε⌋ … ⌊C / ε⌋`, each paired with the internal level set `{y | ⌊g i y / ε⌋ = k}`.

The index set depends on `C` and `ε` only. That is the whole point: the same finite list
serves every stage, so `stepMap` of it is a genuine internal step map rather than a
stagewise finite range, which would be automatic and useless. -/
noncomputable def quantizer (ε C : ℝ) (g : (i : ι) → X i → ℝ) : List (ℝ × InternalSet U X) :=
  (Finset.Icc ⌊-C / ε⌋ ⌊C / ε⌋).toList.map fun k : ℤ ↦
    ((k : ℝ) * ε, Filter.Product.ofFun fun i ↦ {y | ⌊g i y / ε⌋ = k})

/-- **The quantizer's step map, stagewise.** At each point, the sum over the codebook of
the level whose cell contains the point.

The list/`Finset` conversion happens here and nowhere else: `stepMap_ofFun` gives a
`List.sum` over `Finset.toList`, and `Finset.sum_map_toList` turns it into a `Finset.sum`. -/
theorem stepMap_quantizer (ε C : ℝ) (g : (i : ι) → X i → ℝ) :
    stepMap (quantizer ε C g : List (ℝ × InternalSet U X))
      = Filter.Product.ofFun fun i y ↦
          ∑ k ∈ Finset.Icc ⌊-C / ε⌋ ⌊C / ε⌋, if ⌊g i y / ε⌋ = k then (k : ℝ) * ε else 0 := by
  have h := stepMap_ofFun (U := U) ((Finset.Icc ⌊-C / ε⌋ ⌊C / ε⌋).toList.map fun k : ℤ ↦
    ((k : ℝ) * ε, fun i ↦ {y | ⌊g i y / ε⌋ = k}))
  simp only [List.map_map, Function.comp_def] at h
  rw [quantizer, h]
  congr 1
  funext i y
  rw [Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [Set.indicator_apply]

/-- Where the bound holds, the codebook sum collapses to the one matching level. -/
private theorem sum_quantizer_eq {ε C : ℝ} (hε : 0 < ε) {t : ℝ} (ht : ‖t‖ ≤ C) :
    (∑ k ∈ Finset.Icc ⌊-C / ε⌋ ⌊C / ε⌋, if ⌊t / ε⌋ = k then (k : ℝ) * ε else 0)
      = ⌊t / ε⌋ * ε := by
  rw [Finset.sum_ite_eq, if_pos]
  rw [Real.norm_eq_abs, abs_le] at ht
  exact Finset.mem_Icc.2 ⟨Int.floor_mono (div_le_div_of_nonneg_right ht.1 hε.le),
    Int.floor_mono (div_le_div_of_nonneg_right ht.2 hε.le)⟩

/-- **Uniform step approximation, at the representative level.**

For a stagewise family eventually bounded by `C` and any mesh `0 < ε`, a step map with a
stage-independent codebook — namely `quantizer ε C g` — is within `ε` of `g` at every point
of every stage where the bound holds. The step map is returned with a representative in
hand, which is the form the two transfer arguments below consume; its boundedness is
`isUniformlyBounded_stepMap`.

No stage instances, no `hU`, no `hX`. -/
theorem exists_stepMap_eventually_abs_sub_lt {g : (i : ι) → X i → ℝ} {C : ℝ}
    (hC : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (l : List (ℝ × InternalSet U X)) (q : (i : ι) → X i → ℝ),
      stepMap l = Filter.Product.ofFun q
        ∧ ∀ᶠ i in (U : Filter ι), ∀ y, |g i y - q i y| < ε :=
  ⟨quantizer ε C g, _, stepMap_quantizer ε C g, hC.mono fun i hi y ↦ by
    rw [sum_quantizer_eq hε (hi y)]
    exact abs_sub_floor_div_mul_lt hε _⟩

section Stage

variable [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- **Uniform step approximation, on both sides.**

A uniformly bounded internal map is within `ε` of a step map at every point of the lift
*and* in the mean. The two transfers are separate — the first through F0's bounded
ultralimit arithmetic on values, the second through F3a's mean laws — because the two
linearities are separate facts.

The bound is `≤ ε`, not `< ε`: the stagewise error is strict, but limits do not preserve
strictness, and the identity only needs the weak form. No `hU`, no `hX`. -/
theorem exists_stepMap_abs_sub_le {f : InternalMap U X fun _ ↦ ℝ} (hf : f.IsUniformlyBounded)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (ℝ × InternalSet U X),
      (∀ x, |lift f x - lift (stepMap l) x| ≤ ε)
        ∧ |internalMean f - internalMean (stepMap l)| ≤ ε := by
  induction f using Filter.Product.inductionOn with
  | _ g =>
    obtain ⟨C, hC⟩ := (isUniformlyBounded_ofFun g).1 hf
    obtain ⟨l, q, hl, hq⟩ := exists_stepMap_eventually_abs_sub_lt hC hε
    -- The approximant inherits a bound from `g` and the error.
    have hqC : ∀ᶠ i in (U : Filter ι), ∀ y, ‖q i y‖ ≤ C + ε := by
      filter_upwards [hC, hq] with i hi hi' y
      have h1 := hi y
      have h2 := hi' y
      rw [Real.norm_eq_abs] at h1 ⊢
      linarith [abs_sub_abs_le_abs_sub (q i y) (g i y), abs_sub_comm (q i y) (g i y)]
    have hqb : IsUniformlyBounded (Filter.Product.ofFun q : InternalMap U X fun _ ↦ ℝ) :=
      (isUniformlyBounded_ofFun q).2 ⟨C + ε, hqC⟩
    have hgb : IsUniformlyBounded (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ) :=
      (isUniformlyBounded_ofFun g).2 ⟨C, hC⟩
    refine ⟨l, fun x ↦ ?_, ?_⟩
    · -- Values: the difference of ultralimits is the ultralimit of the difference.
      induction x using Filter.Product.inductionOn with
      | _ x' =>
        rw [hl, lift_ofFun, lift_ofFun, sub_eq_add_neg,
          ← Ultrafilter.ultralimit_neg_of_eventually_norm_le (hqC.mono fun i hi ↦ hi (x' i)),
          ← Ultrafilter.ultralimit_add_of_eventually_norm_le (hC.mono fun i hi ↦ hi (x' i))
            (hqC.mono fun i hi ↦ by simpa using hi (x' i))]
        exact Ultrafilter.abs_ultralimit_le (hq.mono fun i hi ↦ by
          simpa [sub_eq_add_neg] using (hi (x' i)).le)
    · -- Means: the difference of means is the mean of the difference.
      rw [hl, show internalMean (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ)
          - internalMean (Filter.Product.ofFun q : InternalMap U X fun _ ↦ ℝ)
          = internalMean (add (Filter.Product.ofFun g) (constMul (-1) (Filter.Product.ofFun q)))
          by rw [internalMean_add hgb (hqb.constMul (-1)), internalMean_constMul (-1) hqb]; ring,
        constMul_ofFun, add_ofFun, ← Real.norm_eq_abs]
      refine norm_internalMean_ofFun_le hε.le (hq.mono fun i hi y ↦ ?_)
      have : g i y + -1 * q i y = g i y - q i y := by ring
      rw [Pi.add_apply, this, Real.norm_eq_abs]
      exact (hi y).le

/-! ### The identity -/

/-- **The integral identity.** The Loeb integral of the lift of a uniformly bounded
internal map is the ultralimit of its stagewise averages.

Both sides are within `ε / 2` of the corresponding side for a step map, the identity holds
for step maps, and the Loeb measure is a probability measure — so the two sides are within
`ε` for every `ε > 0`.

`hU` and `hX` enter only through `loebMeasure`; countable incompleteness is not used
directly. Nothing from saturation or the M3 approximation layer is involved. -/
theorem integral_lift (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    {f : InternalMap U X fun _ ↦ ℝ} (hf : f.IsUniformlyBounded) :
    ∫ x, lift f x ∂(loebMeasure hU hX) = internalMean f := by
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  obtain ⟨l, hlift, hmean⟩ := exists_stepMap_abs_sub_le hf (half_pos hε)
  have hint : dist (∫ x, lift f x ∂(loebMeasure hU hX))
      (∫ x, lift (stepMap l) x ∂(loebMeasure hU hX)) ≤ ε / 2 := by
    rw [dist_eq_norm, ← integral_sub (integrable_lift hU hX hf)
      (integrable_lift hU hX (isUniformlyBounded_stepMap l))]
    calc _ ≤ ε / 2 * (loebMeasure hU hX).real Set.univ :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun x ↦ by
            rw [Real.norm_eq_abs]; exact hlift x)
      _ = ε / 2 := by rw [probReal_univ, mul_one]
  calc dist (∫ x, lift f x ∂(loebMeasure hU hX)) (internalMean f)
      ≤ dist (∫ x, lift f x ∂(loebMeasure hU hX)) (∫ x, lift (stepMap l) x ∂(loebMeasure hU hX))
        + dist (∫ x, lift (stepMap l) x ∂(loebMeasure hU hX)) (internalMean (stepMap l))
        + dist (internalMean (stepMap l)) (internalMean f) := dist_triangle4 _ _ _ _
    _ ≤ ε / 2 + 0 + ε / 2 := by
        refine add_le_add (add_le_add hint ?_) ?_
        · rw [integral_lift_stepMap hU hX l, dist_self]
        · rw [dist_comm, Real.dist_eq]; exact hmean
    _ = ε := by ring

/-- **The representative formula.** For a stagewise family with an eventual bound, the
Loeb integral of its lift is the ultralimit of the stage integrals against the normalized
counting measures. The right-hand side is `internalMean_ofFun`, definitionally. -/
theorem integral_lift_ofFun (hU : (U : Filter ι).IsCountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) {g : (i : ι) → X i → ℝ} {C : ℝ}
    (hC : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C) :
    ∫ x, lift (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ) x ∂(loebMeasure hU hX)
      = U.ultralimit fun i ↦ ∫ y, g i y ∂normalizedCounting (X i) :=
  integral_lift hU hX ((isUniformlyBounded_ofFun g).2 ⟨C, hC⟩)

/-- **The normalized finite-sum formula.** The Loeb integral of the lift is the ultralimit
of the stagewise normalized sums `(1 / |X i|) * ∑ y, g i y`.

`Fintype` on the stages, since the right-hand side is a `Finset.sum`; the ambient `Finite`
is implied and coexists harmlessly, being a proposition. -/
theorem integral_lift_ofFun_eq_ultralimit_sum [∀ i, Fintype (X i)]
    (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    {g : (i : ι) → X i → ℝ} {C : ℝ} (hC : ∀ᶠ i in (U : Filter ι), ∀ y, ‖g i y‖ ≤ C) :
    ∫ x, lift (Filter.Product.ofFun g : InternalMap U X fun _ ↦ ℝ) x ∂(loebMeasure hU hX)
      = U.ultralimit fun i ↦ (1 / Fintype.card (X i) : ℝ) * ∑ y, g i y := by
  rw [integral_lift_ofFun hU hX hC]
  exact Ultrafilter.ultralimit_congr
    (Eventually.of_forall fun i ↦ integral_normalizedCounting (g i))

end Stage

end InternalMap

/-! ### Bundled wrapper -/

namespace BoundedInternalFunction

variable [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- **The integral identity**, bundled. -/
theorem integral_lift (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (f : BoundedInternalFunction U X) :
    ∫ x, f.lift x ∂(loebMeasure hU hX) = f.internalMean :=
  InternalMap.integral_lift hU hX f.2

end BoundedInternalFunction

/-! ### API tests

The general theorem is exercised beyond the indicators and step maps that earlier units
already cover. -/

section Tests

variable [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- **The finite-stage formula on `Empty`.** Both sides are `0`; no nonemptiness is
assumed, and none is available. -/
example (g : Empty → ℝ) : ∫ y, g y ∂normalizedCounting Empty = 0 := by
  rw [integral_normalizedCounting]
  simp

/-- The finite-stage formula, on a concrete stage. -/
example (g : Fin 4 → ℝ) : ∫ y, g y ∂normalizedCounting (Fin 4) = (1 / 4 : ℝ) * ∑ y, g y := by
  rw [integral_normalizedCounting, Fintype.card_fin]
  norm_num

/-- **A family whose stagewise ranges grow.** On stage `n` the values `y / (n + 1)` for
`y : Fin (n + 1)` are `n + 1` distinct points filling out `[0, 1)` — the range is not
finite uniformly in `n`, so nothing about it is a step map, and the identity is the
general theorem's. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete) :
    ∫ x, InternalMap.lift (Filter.Product.ofFun fun n (y : Fin (n + 1)) ↦ (y : ℝ) / (n + 1)
        : InternalMap U (fun n ↦ Fin (n + 1)) fun _ ↦ ℝ) x ∂(loebMeasure hU fun _ ↦ inferInstance)
      = U.ultralimit fun n ↦ (1 / Fintype.card (Fin (n + 1)) : ℝ)
          * ∑ y : Fin (n + 1), (y : ℝ) / (n + 1) :=
  InternalMap.integral_lift_ofFun_eq_ultralimit_sum _ _ (C := 1)
    (Eventually.of_forall fun n y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (by positivity)]
      have := y.is_le
      have h : (y : ℝ) ≤ n := by exact_mod_cast this
      linarith)

/-- And the ranges really do grow: stage `n` attains `n / (n + 1)`. -/
example (n : ℕ) : ((Fin.last n : Fin (n + 1)) : ℝ) / (n + 1) = n / (n + 1) := by
  simp

/-- **Eventual-only boundedness.** The family is `n` on even stages and a bounded profile
on odd ones. If the odd stages are `U`-large, the map is uniformly bounded in the eventual
sense and the identity applies — though the family is globally unbounded. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    (hodd : {n | Odd n} ∈ U) :
    ∫ x, InternalMap.lift (Filter.Product.ofFun fun n (y : Fin (n + 1)) ↦
          if Even n then (n : ℝ) else (y : ℝ) / (n + 1)
        : InternalMap U (fun n ↦ Fin (n + 1)) fun _ ↦ ℝ) x ∂(loebMeasure hU fun _ ↦ inferInstance)
      = U.ultralimit fun n ↦ ∫ y : Fin (n + 1),
          (if Even n then (n : ℝ) else (y : ℝ) / (n + 1)) ∂normalizedCounting (Fin (n + 1)) :=
  InternalMap.integral_lift_ofFun _ _ (C := 1)
    (eventually_of_mem hodd fun n hn y ↦ by
      rw [if_neg (Nat.not_even_iff_odd.2 hn), Real.norm_eq_abs, abs_of_nonneg (by positivity),
        div_le_one (by positivity)]
      have := y.is_le
      have h : (y : ℝ) ≤ n := by exact_mod_cast this
      linarith)

/-- And that family is genuinely unbounded, so the previous test is about the eventual
notion and not a pointwise one. -/
example : ¬ ∃ C : ℝ, ∀ n (y : Fin (n + 1)),
    ‖if Even n then (n : ℝ) else (y : ℝ) / (n + 1)‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC (2 * n) 0
  rw [if_pos (even_two_mul n), Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
  push_cast at this
  linarith

/-- The quantizer's codebook is stage-independent: its length is a function of `ε` and `C`
alone, and in particular does not mention the family. -/
example (ε C : ℝ) (g : (i : ι) → X i → ℝ) :
    (InternalMap.quantizer ε C g : List (ℝ × InternalSet U X)).length
      = (Finset.Icc ⌊-C / ε⌋ ⌊C / ε⌋).card := by
  rw [InternalMap.quantizer, List.length_map, Finset.length_toList]

/-- The bundled identity. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (f : BoundedInternalFunction U X) :
    ∫ x, f.lift x ∂(loebMeasure hU hX) = f.internalMean :=
  BoundedInternalFunction.integral_lift hU hX f

/-- The approximation theorem takes neither `hU` nor `hX`. -/
example {f : InternalMap U X fun _ ↦ ℝ} (hf : f.IsUniformlyBounded) :
    ∃ l : List (ℝ × InternalSet U X),
      (∀ x, |InternalMap.lift f x - InternalMap.lift (InternalMap.stepMap l) x| ≤ 1)
        ∧ |InternalMap.internalMean f - InternalMap.internalMean (InternalMap.stepMap l)| ≤ 1 :=
  InternalMap.exists_stepMap_abs_sub_le hf one_pos

end Tests

end Loeb
