/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.GraphLimit.HomEvent
import LoebMeasure.Measure.Loeb

/-!
# The homomorphism density identity

The Loeb measure of the internal homomorphism event is the ultralimit of the finite
homomorphism densities. This is M4's theorem, and the first finite-to-Loeb result in the
project.

## Three statements at three hypothesis levels

The unit is deliberately split so that each ingredient carries only what it needs:

* `finiteHomDensity` — **finite target only**. No measurable structure and no
  nonemptiness: it is a ratio of cardinalities;
* `normalizedCounting_homomorphismSet` — adds the **discrete measurable structure**
  (`MeasurableSpace` and `MeasurableSingletonClass`) needed for `normalizedCounting`, and
  nothing else. Still no nonemptiness. This is the substantive step;
* `loebMeasure_internalHomEvent` — adds `hU` and nonemptiness, because `loebMeasure`
  requires them.

## Why the density is defined independently of measure theory

`finiteHomDensity F G` is `(homomorphismSet F G).ncard / (Nat.card X) ^ k` in `ℝ≥0∞`,
written out rather than defined as the `normalizedCounting` value. Defining it as the
latter would make `normalizedCounting_homomorphismSet` true by definition and would verify
nothing — in particular it would not check that the normalization is the intended
`|X| ^ k`.

That check is the content of the stage identity. The stage measure lives on `Fin k → X`,
so `normalizedCounting` normalizes by `Nat.card (Fin k → X)`, and the identity holds
because `Nat.card_fun` and `Nat.card_fin` say that is `Nat.card X ^ k`. Had the
normalization been wrong, the theorem would fail rather than hold vacuously.

## What the Loeb step costs

Almost nothing, which is the point of M4 preceding the integration layers. G2's
`internalHomEvent_eq_ofFun` puts the event in `ofFun` form, `loebMeasure_internal` sends
the measure of a realized internal set to its content, and `internalContent_ofFun` sends
that content to the ultralimit of the stagewise `normalizedCounting` values. The stage
identity then rewrites under the ultralimit. No integration, and no ordinary product
measurability.

## Which side is measured

The event lives on `Ultraproduct U (fun i ↦ Fin k → X i)` — the ultraproduct of stagewise
powers — so this is the Loeb measure of *that* space, not of `Ultraproduct U X`. That is
the side internality is defined on throughout the project, and keeping the theorem there
is what avoids any appeal to ordinary product measurability.

## Nonemptiness

`loebMeasure` on the powers needs `∀ i, Nonempty (Fin k → X i)`, which is what the theorem
takes. That is *weaker* than stage nonemptiness and worth stating that way: it follows from
`∀ i, Nonempty (X i)`, but for `k = 0` it holds outright, since the empty tuple exists over
any stage.

## Scope

The density identity. No `SimpleGraph.Hom` packaging, no integration, no graphon
realization.
-/

namespace Loeb

open Filter MeasureTheory
open scoped ENNReal

/-! ### The finite density -/

/-- **The finite homomorphism density**: the proportion of vertex maps `Fin k → X` that
preserve every edge of `F`.

Counts **all** edge-preserving maps — neither induced nor injective — and normalizes by
`|X| ^ k`, the number of vertex maps. Needs a finite target and nothing else. -/
noncomputable def finiteHomDensity {k : ℕ} {X : Type*} [Finite X] (F : SimpleGraph (Fin k))
    (G : SimpleGraph X) : ℝ≥0∞ :=
  ((homomorphismSet F G).ncard : ℝ≥0∞) / (Nat.card X : ℝ≥0∞) ^ k

/-- **With no pattern edges the density is one.** Every map is a homomorphism, and there
are `|X| ^ k` of them.

Compiled rather than left to the general theorem: it is the case where the normalization
must cancel exactly, so it checks the denominator rather than merely elaborating. -/
@[simp]
theorem finiteHomDensity_bot {k : ℕ} {X : Type*} [Finite X] [Nonempty X]
    (G : SimpleGraph X) :
    finiteHomDensity (⊥ : SimpleGraph (Fin k)) G = 1 := by
  classical
  haveI := Fintype.ofFinite X
  rw [finiteHomDensity, homomorphismSet_bot, Set.ncard_univ, Nat.card_fun, Nat.card_fin,
    Nat.cast_pow, ENNReal.div_self]
  · exact pow_ne_zero _ (by exact_mod_cast Nat.card_pos.ne')
  · exact ENNReal.pow_ne_top (by simp)

/-- **The empty pattern gives density one**, with no nonemptiness of the target at all:
over `Fin 0` the only vertex map is the empty tuple, and it is vacuously a homomorphism.

This is the degenerate case the general theorem must not need a side condition for. -/
@[simp]
theorem finiteHomDensity_of_isEmpty {X : Type*} [Finite X] (F : SimpleGraph (Fin 0))
    (G : SimpleGraph X) : finiteHomDensity F G = 1 := by
  have h : homomorphismSet F G = Set.univ := by
    ext f
    simp only [mem_homomorphismSet, Set.mem_univ, iff_true]
    exact fun u ↦ (Fin.elim0 u)
  rw [finiteHomDensity, h, Set.ncard_univ, pow_zero, Nat.card_fun, Nat.card_fin, pow_zero,
    Nat.cast_one, div_one]

/-! ### The stage identity

The substantive step, and the one that checks the normalization. -/

/-- **The stagewise counting identity.**

The normalized counting measure of the homomorphism set, taken on the power `Fin k → X`,
*is* the finite homomorphism density.

This is where the normalization is verified: `normalizedCounting` divides by
`Nat.card (Fin k → X)`, and the identity holds precisely because `Nat.card_fun` and
`Nat.card_fin` identify that with `Nat.card X ^ k`. Since `finiteHomDensity` was defined
independently, a wrong normalization would break this rather than hide in it.

Adds the discrete measurable structure and nothing else — in particular **no
nonemptiness**. On an empty target both sides are `0 / 0 = 0` for `k > 0`, and `1` for
`k = 0`. -/
theorem normalizedCounting_homomorphismSet {k : ℕ} {X : Type*} [MeasurableSpace X]
    [Finite X] [MeasurableSingletonClass X] (F : SimpleGraph (Fin k)) (G : SimpleGraph X) :
    normalizedCounting (Fin k → X) (homomorphismSet F G) = finiteHomDensity F G := by
  rw [normalizedCounting_apply_natCard, finiteHomDensity, Nat.card_fun, Nat.card_fin,
    Nat.cast_pow]

/-! ### The Loeb identity -/

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] {U : Ultrafilter ι} {k : ℕ}

/-- **The homomorphism density identity** — M4's theorem.

The Loeb measure of the internal homomorphism event equals the ultralimit of the finite
homomorphism densities.

The measure is taken on `Ultraproduct U (fun i ↦ Fin k → X i)`, the ultraproduct of
stagewise powers, which is the side internality lives on. No ordinary product
measurability is assumed anywhere, and no integration is used: the proof is
`internalHomEvent_eq_ofFun`, then `loebMeasure_internal`, then `internalContent_ofFun`,
then the stage identity under the ultralimit.

The nonemptiness hypothesis is on the *powers*, which is weaker than stage nonemptiness
and automatic when `k = 0`. -/
theorem loebMeasure_internalHomEvent (hU : (U : Filter ι).IsCountablyIncomplete)
    (hXk : ∀ i, Nonempty (Fin k → X i)) (F : SimpleGraph (Fin k))
    (G : ∀ i, SimpleGraph (X i)) :
    loebMeasure (X := fun i ↦ Fin k → X i) hU hXk
        (InternalSet.carrier (internalHomEvent U F G))
      = U.ultralimit fun i ↦ finiteHomDensity F (G i) := by
  rw [internalHomEvent_eq_ofFun, loebMeasure_internal, internalContent_ofFun]
  exact Ultrafilter.ultralimit_congr
    (Eventually.of_forall fun i ↦ normalizedCounting_homomorphismSet F (G i))

omit [∀ i, MeasurableSpace (X i)] [∀ i, Finite (X i)]
  [∀ i, MeasurableSingletonClass (X i)] in
/-- Stage nonemptiness gives nonempty stage powers, which is what the theorem above takes.
Stated so callers holding the usual `hX` need not build the tuple by hand. -/
theorem nonempty_pi_of_nonempty (hX : ∀ i, Nonempty (X i)) (i : ι) :
    Nonempty (Fin k → X i) :=
  ⟨fun _ ↦ (hX i).some⟩

/-! ### API tests -/

section Tests

/-- **M4's theorem**, in the shape the roadmap gate names, from ordinary stage
nonemptiness. -/
example (hU : (U : Filter ι).IsCountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (F : SimpleGraph (Fin k)) (G : ∀ i, SimpleGraph (X i)) :
    loebMeasure (X := fun i ↦ Fin k → X i) hU (nonempty_pi_of_nonempty hX)
        (InternalSet.carrier (internalHomEvent U F G))
      = U.ultralimit fun i ↦ finiteHomDensity F (G i) :=
  loebMeasure_internalHomEvent hU _ F G

/-- **`k = 0` gives density one**, computed rather than merely elaborated: the empty tuple
is the unique vertex map and is vacuously a homomorphism, so the numerator and the
denominator `|X| ^ 0` both equal `1`. -/
example (X : Type) [Finite X] (F : SimpleGraph (Fin 0)) (G : SimpleGraph X) :
    finiteHomDensity F G = 1 := by
  simp

/-- **And `k = 0` needs no nonemptiness**, on a stage family that is empty at every
index — the empty tuple exists regardless, so the Loeb identity applies. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    (F : SimpleGraph (Fin 0)) (G : ∀ _ : ℕ, SimpleGraph (Empty)) :
    loebMeasure (X := fun _ : ℕ ↦ Fin 0 → Empty) hU (fun _ ↦ ⟨Fin.elim0⟩)
        (InternalSet.carrier (internalHomEvent U F G))
      = U.ultralimit fun _ ↦ (1 : ℝ≥0∞) := by
  rw [loebMeasure_internalHomEvent]
  exact Ultrafilter.ultralimit_congr (Eventually.of_forall fun _ ↦ by simp)

/-- **The stage identity on its own**, at its own hypothesis level: discrete measurable
structure, no nonemptiness. -/
example (Y : Type) [MeasurableSpace Y] [Finite Y] [MeasurableSingletonClass Y]
    (F : SimpleGraph (Fin k)) (G : SimpleGraph Y) :
    normalizedCounting (Fin k → Y) (homomorphismSet F G) = finiteHomDensity F G :=
  normalizedCounting_homomorphismSet F G

/-- **The density needs only a finite target** — no measurable structure in sight, which
is why this statement elaborates at all. -/
example (Y : Type) [Finite Y] (F : SimpleGraph (Fin k)) (G : SimpleGraph Y) :
    finiteHomDensity F G = ((homomorphismSet F G).ncard : ℝ≥0∞) / (Nat.card Y : ℝ≥0∞) ^ k :=
  rfl

/-- **A genuinely dependent family** of stage graphs on varying vertex types, which is the
setting M4 exists for. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).IsCountablyIncomplete)
    (F : SimpleGraph (Fin 3)) (G : ∀ i : ℕ, SimpleGraph (Fin (i + 1))) :
    loebMeasure (X := fun i : ℕ ↦ Fin 3 → Fin (i + 1)) hU (fun _ ↦ ⟨fun _ ↦ 0⟩)
        (InternalSet.carrier (internalHomEvent U F G))
      = U.ultralimit fun i ↦ finiteHomDensity F (G i) :=
  loebMeasure_internalHomEvent hU _ F G

/-- The density is a probability value, as it must be for the identity to be consistent
with `loebMeasure` being a probability measure. -/
example (Y : Type) [MeasurableSpace Y] [Finite Y] [MeasurableSingletonClass Y]
    (F : SimpleGraph (Fin k)) (G : SimpleGraph Y) : finiteHomDensity F G ≤ 1 := by
  rw [← normalizedCounting_homomorphismSet]
  exact normalizedCounting_le_one _

end Tests

end Loeb
