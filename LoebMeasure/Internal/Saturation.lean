/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.BooleanAlgebra
import LoebMeasure.Internal.Diagonal

/-!
# Internal saturation

Countable saturation for internal sets: a decreasing sequence of nonempty internal sets
has nonempty intersection, and — the form the measure layer consumes — a decreasing
sequence whose carriers meet emptily is *eventually* the bottom internal set.

That last statement is **continuity at `∅` in combinatorial dress**. It is what makes
`MeasureTheory.addContent_iUnion_eq_sum_of_tendsto_zero` applicable at M3: saturation
does not merely make the contents tend to zero, it makes the sequence eventually empty
outright.

## The hypothesis ladder

Each result adds exactly one thing to the one before it, and the docstrings say which:

| Result | Adds |
| --- | --- |
| I5's `exists_forall_eventually_mem` | countable incompleteness, nonempty fibers |
| `nonempty_iInter_carrier_of_antitone` | nothing — no dichotomy reasoning |
| `nonempty_iInter_carrier_of_ne_bot` | the **ultrafilter dichotomy**, via carrier faithfulness |
| `eventually_eq_bot_of_antitone_iInter_...` | nothing — it is the contrapositive |

Nothing here mentions content, ultralimits, or measure. The increasing-envelope theorem
is deliberately **not** here: Elek–Szegedy's Lemma 2.4 preserves the *limiting internal
content*, so it cannot be stated before `internalContent` exists and belongs to M3. The
countable null-cover theorem belongs later still, with the null-set layer.
-/

namespace Loeb.InternalSet

open Filter

variable {ι : Type*} {U : Ultrafilter ι} {X : ι → Type*} {A : ℕ → InternalSet U X}

/-- **Countable saturation, carrier form.** A decreasing sequence of internal sets with
nonempty carriers has nonempty intersection.

Adds nothing to the diagonal selection theorem beyond translating between carriers and
stagewise data: no ultrafilter dichotomy is used, because `carrier_ofFun_nonempty_iff`
supplies eventual stagewise nonemptiness directly from a nonempty carrier. -/
theorem nonempty_iInter_carrier_of_antitone (hU : (U : Filter ι).CountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (hanti : Antitone A)
    (hne : ∀ n, (carrier (A n)).Nonempty) :
    (⋂ n, carrier (A n)).Nonempty := by
  classical
  -- Choose stagewise representatives, then apply diagonal selection to them.
  choose A' hA' using fun n ↦ Filter.Product.exists_ofFun (A n)
  have hne' : ∀ n, ∀ᶠ i in (U : Filter ι), (A' n i).Nonempty := by
    intro n
    exact (carrier_ofFun_nonempty_iff hX (A' n)).1 (hA' n ▸ hne n)
  have hdec : ∀ n, ∀ᶠ i in (U : Filter ι), A' (n + 1) i ⊆ A' n i := by
    intro n
    have hle : (Filter.Product.ofFun (A' (n + 1)) : InternalSet U X)
        ≤ Filter.Product.ofFun (A' n) := by
      rw [← hA' (n + 1), ← hA' n]
      exact hanti (Nat.le_succ n)
    exact (le_ofFun_iff _ _).1 hle
  obtain ⟨x, hx⟩ := hU.exists_forall_eventually_mem hdec hne'
  refine ⟨Filter.Product.ofFun x, Set.mem_iInter.2 fun n ↦ ?_⟩
  rw [hA' n]
  exact (mem_carrier_ofFun x (A' n)).2 (hx n)

/-- **Countable saturation, quotient form.** A decreasing sequence of internal sets that
are not `⊥` has nonempty intersection of carriers.

This is the rung where the **ultrafilter dichotomy** enters, and it enters through
carrier faithfulness: `A n ≠ ⊥` gives `carrier (A n) ≠ ∅` only because `carrier` is
injective, which is `carrier_injective` from I2 — whose proof is where the dichotomy
does its work. -/
theorem nonempty_iInter_carrier_of_ne_bot (hU : (U : Filter ι).CountablyIncomplete)
    (hX : ∀ i, Nonempty (X i)) (hanti : Antitone A) (hne : ∀ n, A n ≠ ⊥) :
    (⋂ n, carrier (A n)).Nonempty := by
  refine nonempty_iInter_carrier_of_antitone hU hX hanti fun n ↦ ?_
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  exact hne n (carrier_injective hX (by rw [hempty, carrier_bot]))

/-- **Continuity at `∅`, in combinatorial dress.**

If a decreasing sequence of internal sets has empty intersection of carriers, the
sequence is *eventually* `⊥` — not merely small. This is the exact form M3's
sigma-subadditivity argument consumes, and it is the contrapositive of the previous
result, adding nothing to its hypotheses. -/
theorem eventually_eq_bot_of_antitone_iInter_carrier_eq_empty
    (hU : (U : Filter ι).CountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hanti : Antitone A) (hempty : ⋂ n, carrier (A n) = ∅) :
    ∀ᶠ n in atTop, A n = ⊥ := by
  by_contra hcon
  refine absurd hempty (Set.nonempty_iff_ne_empty.1 ?_)
  refine nonempty_iInter_carrier_of_ne_bot hU hX hanti fun n ↦ ?_
  -- If some later term were `⊥`, monotonicity would force every earlier one to be too.
  by_contra hn
  refine hcon ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  exact le_bot_iff.1 (hn ▸ hanti hm)

/-! ### API tests -/

section Tests

/-- The carrier form, applied. -/
example (hU : (U : Filter ι).CountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hanti : Antitone A) (hne : ∀ n, (carrier (A n)).Nonempty) :
    (⋂ n, carrier (A n)).Nonempty :=
  nonempty_iInter_carrier_of_antitone hU hX hanti hne

/-- **The form M3 consumes**: empty intersection forces eventual `⊥`, which is
continuity at `∅` for the internal content. -/
example (hU : (U : Filter ι).CountablyIncomplete) (hX : ∀ i, Nonempty (X i))
    (hanti : Antitone A) (hempty : ⋂ n, carrier (A n) = ∅) :
    ∃ N, ∀ n ≥ N, A n = ⊥ :=
  (eventually_eq_bot_of_antitone_iInter_carrier_eq_empty hU hX hanti hempty).exists_forall_of_atTop

/-- **A genuinely dependent family**, at the canonical hyperfilter. -/
example (X : ℕ → Type) (hX : ∀ i, Nonempty (X i))
    (A : ℕ → InternalSet (Filter.hyperfilter ℕ) X) (hanti : Antitone A)
    (hne : ∀ n, A n ≠ ⊥) :
    (⋂ n, carrier (A n)).Nonempty :=
  nonempty_iInter_carrier_of_ne_bot Filter.hyperfilter_countablyIncomplete hX hanti hne

end Tests

end Loeb.InternalSet
