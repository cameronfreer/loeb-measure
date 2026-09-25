/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Graded.Power
import LoebMeasure.Mathlib.MeasureTheory.OuterMeasure.Induced

/-!
# Permutation invariance of the Loeb power spaces

For `σ : Equiv.Perm (Fin n)`, the coordinate permutation

```
pσ x = x ∘ σ
```

of `Fin n → Ultraproduct U X` is a measurable self-equivalence of the degree-`n` Loeb
space and preserves the degree-`n` Loeb measure — on **every** set, measurable or not,
and in particular on the whole completed σ-algebra rather than only on realized internal
relations.

## The route

Upwards from the stages, and the hypotheses grow with the height:

1. **Stage counting.** Precomposition by `σ` is a bijection of each stage power, so
   normalized counting is invariant (`normalizedCounting_preimage_equiv`).
2. **Internal content.** The stagewise equality passes through the ultralimit:
   `internalContent_comap_perm`. No explicit hypotheses at all.
3. **Loeb outer measure.** `Filter.Product.permute σ` preserves the realized internal
   sets and their content, hence the induced outer measure of every set:
   `loebOuterMeasure_preimage_permute`. Takes `hXn` only.
4. **Carathéodory measurability**, then P2's realization transport:
   `measurableSet_preimage_permute`, `permuteEquiv`, and finally
   `powerMeasure_preimage_perm` and `measurePreserving_perm`, which take `hU`.

The trap at step 3 is that mathlib's `inducedOuterMeasure_preimage` requires the
generating family to be closed under countable unions. Internal carriers need not be, and
that hypothesis is unavailable in general — I3 gives them only a ring. The mirror lemma
`inducedOuterMeasure_preimage_of_injective` needs only injectivity,
which `permute σ` has because `permute σ⁻¹` inverts it. That machinery stays behind the
public statements here; nothing imports the internal-mod-null approximation to obtain
measurability.

## Naming

Two actions appear. On the ultraproduct of stage powers, the action is U5's
`Filter.Product.permute σ`, and lemma names say `permute`. On realized tuples, the action
is precomposition `fun x ↦ x ∘ σ`, written out rather than named — matching
`InternalRelation.tupleCarrier_comap` — and lemma names say `perm`. The two are
intertwined by `Filter.Product.finPowerEquiv_permute`, consumed in a single private
lemma.

The composition convention is the contravariant one fixed in D0.4:
`p(σ * τ) = pτ ∘ pσ`, as `permuteEquiv_mul_apply` states. No `MulAction` instance is
registered.

## Scope

Permutations of a single degree. Cross-degree projections, the canonical split, sections
and Fubini are later units.
-/

namespace Loeb.Graded

open Filter MeasureTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} {U : Ultrafilter ι} [∀ i, MeasurableSpace (X i)]
  [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] {n : ℕ}

/-! ### Internal content -/

/-- **The internal content is permutation invariant.** Stagewise, pulling back along a
permutation of coordinates is a bijection of the stage power, so normalized counting is
unchanged, and the equality passes through the ultralimit. No explicit hypotheses. -/
@[simp]
theorem internalContent_comap_perm (σ : Equiv.Perm (Fin n)) (R : InternalRelation U X n) :
    internalContent U (R.comap σ) = internalContent U R := by
  induction R using Filter.Product.inductionOn with
  | _ A =>
    rw [InternalRelation.comap, InternalSet.preimage_ofFun, internalContent_ofFun,
      internalContent_ofFun]
    exact Ultrafilter.ultralimit_congr (Eventually.of_forall fun i ↦
      normalizedCounting_preimage_equiv (Equiv.arrowCongr σ.symm (Equiv.refl (X i))) (A i))

/-! ### The Loeb outer measure and σ-algebra on the ultraproduct of powers -/

omit [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
/-- Pulling a realized internal relation back along `permute σ` realizes its coordinate
pullback: `InternalRelation.carrier_comap`, read for a permutation. -/
private theorem preimage_permute_carrier (σ : Equiv.Perm (Fin n)) (R : InternalRelation U X n) :
    Filter.Product.permute (l := (U : Filter ι)) (X := X) σ ⁻¹' InternalSet.carrier R
      = InternalSet.carrier (R.comap σ) :=
  (InternalRelation.carrier_comap (σ : Fin n → Fin n) R).symm

omit [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
private theorem preimage_permute_inv_preimage_permute (σ : Equiv.Perm (Fin n))
    (s : Set (Ultraproduct U fun i ↦ Fin n → X i)) :
    Filter.Product.permute σ⁻¹ ⁻¹' (Filter.Product.permute σ ⁻¹' s) = s := by
  ext x
  simp

/-- **The Loeb outer measure on the ultraproduct of powers is permutation invariant**, on
every set. Through `inducedOuterMeasure_preimage_of_injective`: `permute σ` is injective,
preserves the family of realized internal sets, and preserves their content. Takes `hXn`
only. -/
theorem loebOuterMeasure_preimage_permute (hXn : ∀ i, Nonempty (Fin n → X i))
    (σ : Equiv.Perm (Fin n)) (s : Set (Ultraproduct U fun i ↦ Fin n → X i)) :
    loebOuterMeasure hXn (Filter.Product.permute σ ⁻¹' s) = loebOuterMeasure hXn s := by
  refine inducedOuterMeasure_preimage_of_injective
    (Function.LeftInverse.injective (g := Filter.Product.permute σ⁻¹)
      (Filter.Product.permute_permute_symm σ)) (fun t ↦ ?_) (fun t ht ↦ ?_) s
  · constructor
    · rintro ⟨R, hR⟩
      exact ⟨InternalRelation.comap (⇑σ⁻¹) R, by
        rw [← preimage_permute_carrier, hR, preimage_permute_inv_preimage_permute]⟩
    · rintro ⟨R, rfl⟩
      exact ⟨InternalRelation.comap σ R, (preimage_permute_carrier σ R).symm⟩
  · obtain ⟨R, rfl⟩ := ht
    rw [preimage_permute_carrier, internalAddContent_carrier, internalAddContent_carrier,
      internalContent_comap_perm]

/-- **Loeb measurability on the ultraproduct of powers is permutation invariant.**
Carathéodory measurability transports along `permute σ` because the outer measure is
invariant and `permute σ⁻¹` is a left inverse. Takes `hXn` only. -/
theorem measurableSet_preimage_permute (hXn : ∀ i, Nonempty (Fin n → X i))
    (σ : Equiv.Perm (Fin n)) {s : Set (Ultraproduct U fun i ↦ Fin n → X i)}
    (hs : MeasurableSet[loebMeasurableSpace hXn] s) :
    MeasurableSet[loebMeasurableSpace hXn] (Filter.Product.permute σ ⁻¹' s) :=
  OuterMeasure.IsCaratheodory.preimage_of_leftInverse
    (Filter.Product.permute_permute_symm σ) (loebOuterMeasure_preimage_permute hXn σ) hs

/-! ### The measurable self-equivalence of the realized power -/

omit [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)] [∀ i, MeasurableSingletonClass (X i)] in
/-- **How the two actions intertwine under realization**: pulling a tuple set back along
`pσ` and then along the realization is pulling it back along the realization and then
along `permute σ`. This is U5's `finPowerEquiv_permute`, and the only place it is
consumed. -/
private theorem realize_preimage_comp_perm (σ : Equiv.Perm (Fin n))
    (s : Set (Fin n → Ultraproduct U X)) :
    realize (U := U) n ⁻¹' ((fun x ↦ x ∘ σ) ⁻¹' s)
      = Filter.Product.permute σ ⁻¹' (realize n ⁻¹' s) := by
  ext x
  simp only [Set.mem_preimage]
  rw [Filter.Product.finPowerEquiv_permute]
  exact Iff.rfl

/-- **The coordinate permutation as a measurable self-equivalence** of the degree-`n`
Loeb space: `pσ x = x ∘ σ`, with inverse `x ↦ x ∘ ⇑σ⁻¹`. Measurability in both directions
is `measurableSet_preimage_permute` through the realization. Takes `hXn` only. -/
noncomputable def permuteEquiv (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i))
    (σ : Equiv.Perm (Fin n)) :
    @MeasurableEquiv (Fin n → Ultraproduct U X) (Fin n → Ultraproduct U X)
      (powerMeasurableSpace n hXn) (powerMeasurableSpace n hXn) :=
  letI := powerMeasurableSpace (U := U) n hXn
  { toFun := fun x ↦ x ∘ σ
    invFun := fun x ↦ x ∘ ⇑σ⁻¹
    left_inv := fun x ↦ funext fun a ↦ by simp
    right_inv := fun x ↦ funext fun a ↦ by simp
    measurable_toFun := fun s hs ↦ by
      change MeasurableSet[loebMeasurableSpace hXn] (realize n ⁻¹' ((fun x ↦ x ∘ σ) ⁻¹' s))
      rw [realize_preimage_comp_perm]
      exact measurableSet_preimage_permute hXn σ hs
    measurable_invFun := fun s hs ↦ by
      change MeasurableSet[loebMeasurableSpace hXn] (realize n ⁻¹' ((fun x ↦ x ∘ ⇑σ⁻¹) ⁻¹' s))
      rw [realize_preimage_comp_perm]
      exact measurableSet_preimage_permute hXn σ⁻¹ hs }

/-- The forward action is precomposition. The right-hand side is a lambda rather than
`x ∘ σ`, so that a subsequent evaluation or cancellation is a beta-reduction `simp` performs
on its own, instead of a composition it cannot reassociate. -/
@[simp]
theorem permuteEquiv_apply (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i)) (σ : Equiv.Perm (Fin n))
    (x : Fin n → Ultraproduct U X) :
    permuteEquiv n hXn σ x = fun a ↦ x (σ a) :=
  rfl

/-- The inverse action is precomposition by the inverse permutation, in the same lambda
form. Stated with the two spaces explicit, since `.symm` cannot find them otherwise. -/
@[simp]
theorem permuteEquiv_symm_apply (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i))
    (σ : Equiv.Perm (Fin n)) (x : Fin n → Ultraproduct U X) :
    @MeasurableEquiv.symm _ _ (powerMeasurableSpace n hXn) (powerMeasurableSpace n hXn)
      (permuteEquiv n hXn σ) x = fun a ↦ x (σ.symm a) :=
  rfl

/-- The identity permutation acts trivially. -/
@[simp]
theorem permuteEquiv_one_apply (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i))
    (x : Fin n → Ultraproduct U X) :
    permuteEquiv n hXn 1 x = x :=
  rfl

/-- **Contravariance**: `p(σ * τ) = pτ ∘ pσ`, the convention of
`Filter.Product.permute_mul`. Deliberately not a simp lemma, so that rewriting cannot
silently pick an orientation. -/
theorem permuteEquiv_mul_apply (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i))
    (σ τ : Equiv.Perm (Fin n)) (x : Fin n → Ultraproduct U X) :
    permuteEquiv n hXn (σ * τ) x = permuteEquiv n hXn τ (permuteEquiv n hXn σ x) :=
  rfl

/-- **Measurability of the coordinate permutation**, with its spaces explicit. -/
theorem measurable_perm (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i)) (σ : Equiv.Perm (Fin n)) :
    @Measurable (Fin n → Ultraproduct U X) (Fin n → Ultraproduct U X)
      (powerMeasurableSpace n hXn) (powerMeasurableSpace n hXn) (fun x ↦ x ∘ σ) :=
  letI := powerMeasurableSpace (U := U) n hXn
  (permuteEquiv n hXn σ).measurable

/-- **Measurability of tuple sets is permutation invariant.** Takes `hXn` only. -/
theorem measurableSet_preimage_perm (n : ℕ) (hXn : ∀ i, Nonempty (Fin n → X i))
    (σ : Equiv.Perm (Fin n)) {s : Set (Fin n → Ultraproduct U X)}
    (hs : MeasurableSet[powerMeasurableSpace n hXn] s) :
    MeasurableSet[powerMeasurableSpace n hXn] ((fun x ↦ x ∘ σ) ⁻¹' s) :=
  measurable_perm n hXn σ hs

/-! ### The measure -/

/-- **The degree-`n` Loeb measure is permutation invariant on every set.** No
measurability hypothesis on `s`: the transport rule `powerMeasure_apply` holds for every
set, and so does the outer-measure invariance. -/
theorem powerMeasure_preimage_perm (n : ℕ) (hU : (U : Filter ι).IsCountablyIncomplete)
    (hXn : ∀ i, Nonempty (Fin n → X i)) (σ : Equiv.Perm (Fin n))
    (s : Set (Fin n → Ultraproduct U X)) :
    powerMeasure n hU hXn ((fun x ↦ x ∘ σ) ⁻¹' s) = powerMeasure n hU hXn s := by
  rw [powerMeasure_apply, powerMeasure_apply, realize_preimage_comp_perm,
    loebMeasure_eq_loebOuterMeasure, loebMeasure_eq_loebOuterMeasure,
    loebOuterMeasure_preimage_permute]

/-- **The coordinate permutation preserves the degree-`n` Loeb measure.** -/
theorem measurePreserving_perm (n : ℕ) (hU : (U : Filter ι).IsCountablyIncomplete)
    (hXn : ∀ i, Nonempty (Fin n → X i)) (σ : Equiv.Perm (Fin n)) :
    @MeasurePreserving (Fin n → Ultraproduct U X) (Fin n → Ultraproduct U X)
      (powerMeasurableSpace n hXn) (powerMeasurableSpace n hXn) (fun x ↦ x ∘ σ)
      (powerMeasure n hU hXn) (powerMeasure n hU hXn) :=
  letI := powerMeasurableSpace (U := U) n hXn
  { measurable := measurable_perm n hXn σ
    map_eq := Measure.ext fun s hs ↦ by
      rw [Measure.map_apply (measurable_perm n hXn σ) hs, powerMeasure_preimage_perm] }

/-! ### API tests

Measurable spaces are explicit in every statement, as in `LoebMeasure/Graded/Power.lean`. -/

section Tests

/-- Coordinate evaluation, forward and inverse, by bare `simp`. -/
example (hXn : ∀ i, Nonempty (Fin n → X i)) (σ : Equiv.Perm (Fin n))
    (x : Fin n → Ultraproduct U X) (a : Fin n) :
    letI := powerMeasurableSpace (U := U) n hXn
    permuteEquiv n hXn σ x a = x (σ a) ∧ (permuteEquiv n hXn σ).symm x a = x (σ.symm a) := by
  simp

/-- **A three-cycle**, checking coordinates. A swap could not distinguish `σ` from `σ⁻¹`;
this does: `σ` sends `0 ↦ 1`, so `pσ x` reads `x 1` at `0`, while `σ⁻¹` sends `0 ↦ 2`.
The application rules reduce both sides to values of `x`; evaluating the swaps is the
rest. -/
example (hXn : ∀ i, Nonempty (Fin 3 → X i)) (x : Fin 3 → Ultraproduct U X) :
    permuteEquiv 3 hXn (Equiv.swap 0 1 * Equiv.swap 1 2) x 0 = x 1
      ∧ permuteEquiv 3 hXn (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ x 0 = x 2 := by
  simp [Equiv.swap_apply_def]

/-- Forward and inverse round-trips, and the identity, by bare `simp`. -/
example (hXn : ∀ i, Nonempty (Fin n → X i)) (σ : Equiv.Perm (Fin n))
    (x : Fin n → Ultraproduct U X) :
    letI := powerMeasurableSpace (U := U) n hXn
    (permuteEquiv n hXn σ).symm (permuteEquiv n hXn σ x) = x
      ∧ permuteEquiv n hXn σ ((permuteEquiv n hXn σ).symm x) = x
      ∧ permuteEquiv n hXn 1 x = x := by
  simp

/-- The inverse action written out, by `simp`. -/
example (hXn : ∀ i, Nonempty (Fin n → X i)) (σ : Equiv.Perm (Fin n))
    (x : Fin n → Ultraproduct U X) :
    letI := powerMeasurableSpace (U := U) n hXn
    (permuteEquiv n hXn σ).symm x = fun a ↦ x (σ.symm a) := by
  simp

/-- **The contravariant orientation**: `p(σ * τ)` applies `pσ` first. -/
example (hXn : ∀ i, Nonempty (Fin n → X i)) (σ τ : Equiv.Perm (Fin n))
    (x : Fin n → Ultraproduct U X) :
    permuteEquiv n hXn (σ * τ) x = permuteEquiv n hXn τ (permuteEquiv n hXn σ x) :=
  permuteEquiv_mul_apply n hXn σ τ x

/-- **Degree zero over `Empty` stages**: every permutation of `Fin 0` acts trivially, and
the degree-zero measure is preserved. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    (σ : Equiv.Perm (Fin 0)) (x : Fin 0 → Ultraproduct U fun _ ↦ Empty) :
    permuteEquiv (X := fun _ ↦ Empty) 0 (fun _ ↦ ⟨fun a ↦ a.elim0⟩) σ x = x
      ∧ @MeasurePreserving _ _ (powerMeasurableSpace 0 _) (powerMeasurableSpace 0 _)
          (fun x ↦ x ∘ σ) (powerMeasure (X := fun _ ↦ Empty) 0 hU fun _ ↦ ⟨fun a ↦ a.elim0⟩)
          (powerMeasure 0 hU fun _ ↦ ⟨fun a ↦ a.elim0⟩) :=
  ⟨funext fun a ↦ a.elim0, measurePreserving_perm 0 hU _ σ⟩

/-- **Arbitrary-set invariance**: no measurability assumption on `s`. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hXn : ∀ i, Nonempty (Fin n → X i))
    (σ : Equiv.Perm (Fin n)) (s : Set (Fin n → Ultraproduct U X)) :
    powerMeasure n hU hXn ((fun x ↦ x ∘ σ) ⁻¹' s) = powerMeasure n hU hXn s :=
  powerMeasure_preimage_perm n hU hXn σ s

/-- **Internal-relation evaluation agrees along both routes.** Through content
invariance: the permuted tuple carrier is the tuple carrier of the pulled-back relation,
whose content is unchanged. Through measure preservation: the power measure of the
permuted set is the power measure of the set. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hXn : ∀ i, Nonempty (Fin n → X i))
    (σ : Equiv.Perm (Fin n)) (R : InternalRelation U X n) :
    powerMeasure n hU hXn ((fun x ↦ x ∘ σ) ⁻¹' InternalRelation.tupleCarrier R)
      = internalContent U R := by
  rw [← InternalRelation.tupleCarrier_comap, powerMeasure_tupleCarrier,
    internalContent_comap_perm]

example (hU : (U : Filter ι).IsCountablyIncomplete) (hXn : ∀ i, Nonempty (Fin n → X i))
    (σ : Equiv.Perm (Fin n)) (R : InternalRelation U X n) :
    powerMeasure n hU hXn ((fun x ↦ x ∘ σ) ⁻¹' InternalRelation.tupleCarrier R)
      = internalContent U R := by
  rw [powerMeasure_preimage_perm, powerMeasure_tupleCarrier]

/-- Content invariance by `simp`, with no explicit hypotheses in scope. -/
example (σ : Equiv.Perm (Fin n)) (R : InternalRelation U X n) :
    internalContent U (R.comap σ) = internalContent U R := by
  simp

/-- **Measurability with no `hU` in scope**: the measurable equivalence and the
measurability of permuted sets mention only power nonemptiness. -/
example (hXn : ∀ i, Nonempty (Fin n → X i)) (σ : Equiv.Perm (Fin n))
    (s : Set (Fin n → Ultraproduct U X)) (hs : MeasurableSet[powerMeasurableSpace n hXn] s) :
    MeasurableSet[powerMeasurableSpace n hXn] ((fun x ↦ x ∘ σ) ⁻¹' s)
      ∧ @Measurable (Fin n → Ultraproduct U X) (Fin n → Ultraproduct U X)
          (powerMeasurableSpace n hXn) (powerMeasurableSpace n hXn) (fun x ↦ x ∘ ⇑σ⁻¹) :=
  ⟨measurableSet_preimage_perm n hXn σ hs, measurable_perm n hXn σ⁻¹⟩

/-- **A genuinely dependent stage family**, at degree three with the three-cycle. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    (s : Set (Fin 3 → Ultraproduct U fun i ↦ Fin (i + 1))) :
    powerMeasureOfNonempty 3 hU (fun _ ↦ inferInstance)
        ((fun x ↦ x ∘ ⇑(Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3))) ⁻¹' s)
      = powerMeasureOfNonempty 3 hU (fun _ ↦ inferInstance) s :=
  powerMeasure_preimage_perm 3 hU _ (Equiv.swap 0 1 * Equiv.swap 1 2) s

end Tests

end Loeb.Graded
