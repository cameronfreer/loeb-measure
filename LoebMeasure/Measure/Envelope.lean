/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.Diagonal
import LoebMeasure.Measure.Content

/-!
# The internal envelope

**Elek–Szegedy Lemma 2.4.** Any sequence of internal sets is contained in a *single*
internal set whose content is exactly the supremum of the contents of the finite partial
unions. Internality survives a countable union, at no cost in content — which is the
whole reason a finitely additive internal content extends to a measure.

The statement is for an **arbitrary** sequence, not a monotone one: C7b's outer-measure
covers are arbitrary, and the finite partial unions are what make the supremum the right
value.

## Equality, not just an upper bound

`∃ B, (∀ n, A n ≤ B) ∧ internalContent U B = ⨆ n, internalContent U (partialSups A n)`.

The inequality `≥` is free from monotonicity, so the content is the whole point: a
careless envelope — say `⊤` — contains everything and has content `1`. The `≤` half is
what the diagonal argument buys, and it is why the envelope can be used to compute an
outer measure rather than merely to bound one.

## Which hypotheses are used, and which are conspicuously absent

`exists_internal_envelope` takes `hU` and nothing else. Three absences, each structural:

* **no `(hX : ∀ i, Nonempty (X i))`.** The diagonal selector is applied with fibers `ℕ`,
  choosing a *level* at each stage rather than a point of `X i`, so the selector's own
  nonemptiness requirement is discharged by the instance on `ℕ`. Nothing here needs a
  stagewise witness;
* **no `[∀ i, Finite (X i)]`.** The whole module runs on `[∀ i, MeasurableSpace (X i)]`
  alone. This follows C1's shape: `normalizedCounting` is defined and bounded by `1` with
  no finiteness, so the content is too, and the envelope argument only ever compares and
  bounds content values. Finiteness is a hypothesis of *additivity* (C3), not of the
  content itself, and additivity is not used here;
* **no `[∀ i, MeasurableSingletonClass (X i)]`**, for the same reason.

`eventually_coherent` goes further and omits measurability as well: it is a purely
order-theoretic statement about representatives of an increasing sequence.

The countable incompleteness is consumed **directly**, through
`Filter.CountablyIncomplete.exists_forall_eventually_mem`. M2's saturation results are
not used, and cannot be: this module does not import `Internal/Saturation.lean`. Those
results are about descending internal sets with empty intersection, whereas this is an
ascending selection, so routing through them would be a detour.

## How the diagonal selector is applied

The selector is asked for a function `ν : ι → ℕ` assigning to each stage a level, such
that for every `n`, eventually `ν i` is at least `n` *and* level `ν i` is well behaved at
stage `i`. "Well behaved at `(m, i)`" packages the two obligations:

* **coherence** — `∀ j ≤ m, S j i ⊆ S m i`, repairing the fact that representatives of
  an increasing sequence of internal sets are only *eventually* increasing at each level,
  with no uniformity across levels;
* **near-optimal mass** — `normalizedCounting (X i) (S m i) ≤ c + (m + 1)⁻¹`, with `c`
  the target supremum. The tolerance shrinks with the *level*, not with the selector's
  index, which is what lets a single family be antitone in `n` while still forcing the
  limit down to `c`.

Both are eventually satisfiable at level `m = n`, which is all the selector needs. The
envelope is then `B := ofFun fun i ↦ S (ν i) i`, and the two halves fall out: coherence
gives `partialSups A n ≤ B` for every `n`, and the shrinking tolerance gives
`internalContent U B ≤ c + (n + 1)⁻¹` for every `n`.

## Scope

The envelope and nothing else. Outer measures, Carathéodory measurability and
`loebMeasure` are all C7b onward and deliberately absent — this module imports neither
`Measure/Packaging.lean` nor `Measure/Loeb.lean`.
-/

namespace Loeb

open Filter MeasureTheory
open scoped ENNReal

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {U : Ultrafilter ι}

section Envelope

variable {A : ℕ → InternalSet U X}

/-- The target value: the supremum of the contents of the finite partial unions. -/
private noncomputable def envelopeValue (U : Ultrafilter ι) (A : ℕ → InternalSet U X) :
    ℝ≥0∞ :=
  ⨆ n, internalContent U (partialSups A n)

private theorem envelopeValue_le_one : envelopeValue U A ≤ 1 :=
  iSup_le fun _ ↦ internalContent_le_one _

private theorem envelopeValue_ne_top : envelopeValue U A ≠ ∞ :=
  (envelopeValue_le_one.trans_lt (Ne.lt_top ENNReal.one_ne_top)).ne

/-- The stagewise predicate the diagonal selector ranges over: at stage `i`, the levels
`m` that are at least `n`, cohere with all earlier levels, and have near-optimal mass.

Antitone in `n` pointwise — only the `n ≤ m` conjunct mentions `n` — which is what makes
the selector's descent hypothesis free. -/
private def GoodLevel (U : Ultrafilter ι) (A : ℕ → InternalSet U X)
    (S : ℕ → (i : ι) → Set (X i)) (n : ℕ) (i : ι) : Set ℕ :=
  {m | n ≤ m ∧ (∀ j ≤ m, S j i ⊆ S m i) ∧
    normalizedCounting (X i) (S m i) ≤ envelopeValue U A + ((m : ℝ≥0∞) + 1)⁻¹}

omit [∀ i, MeasurableSpace (X i)] in
/-- Eventual coherence at a fixed level: representatives of an increasing sequence of
internal sets are eventually increasing at each level, and finitely many levels can be
intersected. -/
private theorem eventually_coherent {S : ℕ → (i : ι) → Set (X i)}
    (hS : ∀ n, partialSups A n = Filter.Product.ofFun (S n)) (n : ℕ) :
    ∀ᶠ i in (U : Filter ι), ∀ j ≤ n, S j i ⊆ S n i := by
  have hle : ∀ j ≤ n, ∀ᶠ i in (U : Filter ι), S j i ⊆ S n i := by
    intro j hj
    rw [← InternalSet.le_ofFun_iff, ← hS j, ← hS n]
    exact partialSups_monotone A hj
  have := (eventually_all_finset (Finset.range (n + 1))).2 fun j hj ↦
    hle j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  exact this.mono fun i hi j hj ↦ hi j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

/-- Eventual near-optimal mass at a fixed level. The ultralimit of the stagewise masses
is `internalContent U (partialSups A n) ≤ envelopeValue U A`, which is *strictly* below
the tolerance, so the values are eventually below it. -/
private theorem eventually_mass_le {S : ℕ → (i : ι) → Set (X i)}
    (hS : ∀ n, partialSups A n = Filter.Product.ofFun (S n)) (n : ℕ) :
    ∀ᶠ i in (U : Filter ι),
      normalizedCounting (X i) (S n i) ≤ envelopeValue U A + ((n : ℝ≥0∞) + 1)⁻¹ := by
  have hlt : envelopeValue U A < envelopeValue U A + ((n : ℝ≥0∞) + 1)⁻¹ :=
    ENNReal.lt_add_right envelopeValue_ne_top
      (ENNReal.inv_ne_zero.2 (by simp [ENNReal.add_eq_top]))
  have hlim : U.ultralimit (fun i ↦ normalizedCounting (X i) (S n i))
      < envelopeValue U A + ((n : ℝ≥0∞) + 1)⁻¹ := by
    refine lt_of_le_of_lt ?_ hlt
    rw [← internalContent_ofFun (U := U) (S n), ← hS n]
    exact le_iSup (fun k ↦ internalContent U (partialSups A k)) n
  exact (Ultrafilter.tendsto_ultralimit U _).eventually_le_const hlim

/-- Every level of `GoodLevel` is eventually inhabited: take `m = n`. -/
private theorem eventually_goodLevel_nonempty {S : ℕ → (i : ι) → Set (X i)}
    (hS : ∀ n, partialSups A n = Filter.Product.ofFun (S n)) (n : ℕ) :
    ∀ᶠ i in (U : Filter ι), (GoodLevel U A S n i).Nonempty := by
  filter_upwards [eventually_coherent hS n, eventually_mass_le hS n] with i h1 h2
  exact ⟨n, le_rfl, h1, h2⟩

/-- **The internal envelope — Elek–Szegedy Lemma 2.4.**

An arbitrary sequence of internal sets is contained in one internal set whose content is
*exactly* the supremum of the contents of the finite partial unions.

The equality is the substance. The `≥` half is monotonicity, and holds of any envelope;
the `≤` half is what the diagonal selection buys, and it is what makes the envelope
usable to *compute* an outer measure rather than merely to bound one.

Takes `hU` and nothing else — in particular no stage nonemptiness, since the selection
chooses levels in `ℕ` rather than points of the stages. -/
theorem exists_internal_envelope (hU : (U : Filter ι).CountablyIncomplete)
    (A : ℕ → InternalSet U X) :
    ∃ B : InternalSet U X, (∀ n, A n ≤ B) ∧
      internalContent U B = ⨆ n, internalContent U (partialSups A n) := by
  -- Representatives of the partial unions, and the diagonal choice of a level per stage.
  choose S hS using fun n ↦ Filter.Product.exists_ofFun (partialSups A n)
  obtain ⟨ν, hν⟩ := hU.exists_forall_eventually_mem (X := fun _ : ι ↦ ℕ)
    (A := GoodLevel U A S)
    (fun k ↦ Eventually.of_forall fun _ m hm ↦ ⟨Nat.le_of_succ_le hm.1, hm.2⟩)
    (eventually_goodLevel_nonempty hS)
  refine ⟨Filter.Product.ofFun fun i ↦ S (ν i) i, ?_, ?_⟩
  · -- Coherence at the selected level dominates every fixed level.
    intro n
    refine (le_partialSups_of_le A (le_refl n)).trans ?_
    rw [hS n, InternalSet.le_ofFun_iff]
    filter_upwards [hν n] with i hi
    exact hi.2.1 n hi.1
  · -- The tolerance at the selected level shrinks with `n`, forcing the limit down to
    -- `envelopeValue`; the reverse is plain monotonicity.
    refine le_antisymm ?_ (iSup_le fun n ↦ internalContent_mono ?_)
    · change internalContent U _ ≤ envelopeValue U A
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
      have hstep : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (ε : ℝ≥0∞) :=
        (ENNReal.inv_le_inv.2 le_self_add).trans hn.le
      refine le_trans (ultralimit_le_of_le
        (b := envelopeValue U A + ((n : ℝ≥0∞) + 1)⁻¹) ?_) (by gcongr)
      filter_upwards [hν n] with i hi
      exact hi.2.2.trans (by gcongr; exact_mod_cast hi.1)
    · rw [hS n, InternalSet.le_ofFun_iff]
      filter_upwards [hν n] with i hi
      exact hi.2.1 n hi.1

/-- **The monotone special case.** For an increasing sequence the partial unions are the
sequence itself, so the envelope's content is the supremum of the sequence's own
contents. Stated as a corollary rather than as the primary form: C7b's covers are
arbitrary. -/
theorem exists_internal_envelope_of_monotone (hU : (U : Filter ι).CountablyIncomplete)
    {A : ℕ → InternalSet U X} (hA : Monotone A) :
    ∃ B : InternalSet U X, (∀ n, A n ≤ B) ∧
      internalContent U B = ⨆ n, internalContent U (A n) := by
  obtain ⟨B, hle, hval⟩ := exists_internal_envelope hU A
  exact ⟨B, hle, by rwa [hA.partialSups_eq] at hval⟩

/-! ### API tests -/

section Tests

/-- **The envelope contains every term**, which is the internality half. -/
example (hU : (U : Filter ι).CountablyIncomplete) (A : ℕ → InternalSet U X) :
    ∃ B : InternalSet U X, ∀ n, A n ≤ B :=
  let ⟨B, hle, _⟩ := exists_internal_envelope hU A; ⟨B, hle⟩

/-- **The content is preserved exactly**, not merely bounded — the half the diagonal
selection buys, and the reason `⊤` is not an acceptable envelope. -/
example (hU : (U : Filter ι).CountablyIncomplete) (A : ℕ → InternalSet U X) :
    ∃ B : InternalSet U X,
      internalContent U B = ⨆ n, internalContent U (partialSups A n) :=
  let ⟨B, _, hval⟩ := exists_internal_envelope hU A; ⟨B, hval⟩

/-- **No stage nonemptiness is needed**: the statement applies to a family with an empty
stage, where the stage measures have total mass `0`. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).CountablyIncomplete)
    (A : ℕ → InternalSet U fun _ : ℕ ↦ (Empty : Type)) :
    ∃ B, ∀ n, A n ≤ B :=
  let ⟨B, hle, _⟩ := exists_internal_envelope hU A; ⟨B, hle⟩

/-- **No stage finiteness is needed** either: the stages here are infinite. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).CountablyIncomplete)
    (A : ℕ → InternalSet U fun _ : ℕ ↦ ℕ) :
    ∃ B : InternalSet U fun _ : ℕ ↦ ℕ, (∀ n, A n ≤ B) ∧
      internalContent U B = ⨆ n, internalContent U (partialSups A n) :=
  exists_internal_envelope hU A

/-- **A genuinely dependent family** of finite stages, the setting M3 actually uses. -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ).CountablyIncomplete)
    (A : ℕ → InternalSet U fun i ↦ Fin (i + 1)) :
    ∃ B : InternalSet U fun i ↦ Fin (i + 1), (∀ n, A n ≤ B) ∧
      internalContent U B = ⨆ n, internalContent U (partialSups A n) :=
  exists_internal_envelope hU A

/-- The monotone corollary, on the canonical countably incomplete filter. -/
example (A : ℕ → InternalSet (hyperfilter ℕ) fun i ↦ Fin (i + 1)) (hA : Monotone A) :
    ∃ B : InternalSet (hyperfilter ℕ) fun i ↦ Fin (i + 1), (∀ n, A n ≤ B) ∧
      internalContent (hyperfilter ℕ) B
        = ⨆ n, internalContent (hyperfilter ℕ) (A n) :=
  exists_internal_envelope_of_monotone Filter.hyperfilter_countablyIncomplete hA

end Tests

end Envelope

end Loeb
