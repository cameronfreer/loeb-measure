/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Mathlib.Topology.Compactness.Ultralimit
import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Bounded real ultralimits

`ℝ` is not compact, so `Ultrafilter.tendsto_ultralimit` does not apply to real families.
An **eventual** norm bound is what repairs that, and it is the hypothesis every bounded
internal function will carry.

## Extending, not replacing

`Ultrafilter.ultralimit` is unchanged. These are additional entry conditions under which
the *same* object is a genuine limit — not a second limit construction, and no hyperreals.
That is an E5 commitment, and it is what lets the `ℝ≥0∞` results in
`LoebMeasure/Ultralimit/Probability.lean` and the real results here sit side by side over
one definition.

## Why the bound must be eventual

Pointwise boundedness would be unusable downstream. A bounded internal function is a
quotient object, and its representatives may behave arbitrarily off a large set: changing
a representative on a `U`-small set changes nothing about the function but destroys any
pointwise bound. The eventual form is invariant under exactly that, which is why it is the
form stated here and the form `Ultrafilter.ultralimit_congr` composes with.

`ultralimit_pure_norm_le_zero_of_unbounded` below makes the difference concrete rather than
rhetorical: an unbounded family whose ultralimit is nonetheless controlled.

## Hypotheses

None beyond the stated bound. In particular `C` is an arbitrary real with **no `0 ≤ C`
assumption**: for `C < 0` the hypothesis `∀ᶠ i in U, ‖f i‖ ≤ C` cannot hold of a proper
ultrafilter, so the statements are correctly vacuous there and need no separate branch.

Stated for `ℝ` rather than for a proper normed space. The generic compact-set theorem in
the mirror directory already supplies the honest generality; a normed-space wrapper would
be speculative until something asks for it.

## Scope

The two entry conditions and the bound they preserve. Bounded internal functions
themselves are F1, and the Loeb measure enters no earlier than F2.
-/

namespace Ultrafilter

open Filter Topology Metric

variable {ι : Type*} {U : Ultrafilter ι} {f : ι → ℝ} {C : ℝ}

/-- **An eventually bounded real family tends to its ultralimit.**

The bridge that makes `Ultrafilter.ultralimit` usable on `ℝ`: an eventual norm bound puts
`f` eventually inside a closed ball, which is compact because `ℝ` is proper, and
`tendsto_ultralimit_of_eventually_mem_compact` does the rest. No Hausdorff hypothesis is
involved at that step — `ℝ` is of course Hausdorff, but the general theorem does not ask.

`C` is unconstrained in sign; see the module docstring. -/
theorem tendsto_ultralimit_of_eventually_norm_le (h : ∀ᶠ i in U, ‖f i‖ ≤ C) :
    Tendsto f U (𝓝 (U.ultralimit f)) :=
  tendsto_ultralimit_of_eventually_mem_compact (isCompact_closedBall (0 : ℝ) C)
    (h.mono fun _ hi ↦ by simpa [Real.norm_eq_abs, dist_eq_norm] using hi)

/-- **The bound passes to the ultralimit.**

Derived from the convergence above together with closedness of the ball, not by a separate
argument: `le_of_tendsto` applied to the composed `‖·‖`. -/
theorem norm_ultralimit_le (h : ∀ᶠ i in U, ‖f i‖ ≤ C) : ‖U.ultralimit f‖ ≤ C :=
  le_of_tendsto (tendsto_ultralimit_of_eventually_norm_le h).norm h

/-- The two-sided form, which is what an interval-valued family gives directly. -/
theorem abs_ultralimit_le (h : ∀ᶠ i in U, |f i| ≤ C) : |U.ultralimit f| ≤ C :=
  norm_ultralimit_le h

/-! ### API tests -/

section Tests

/-- **The bound is genuinely eventual, not pointwise.**

The pure ultrafilter at `0` on `ℕ`, with `f n = n`: the family is globally unbounded, yet
bounded by `0` on the one set that matters, and the ultralimit's norm is bounded
accordingly. A pointwise hypothesis would prove nothing here. -/
theorem ultralimit_pure_norm_le_zero_of_unbounded :
    ‖(pure 0 : Ultrafilter ℕ).ultralimit (fun n ↦ (n : ℝ))‖ ≤ 0 :=
  norm_ultralimit_le (by simp)

/-- And the family really is unbounded, so the previous statement is not vacuous. -/
example : ¬ ∃ C : ℝ, ∀ n : ℕ, ‖(n : ℝ)‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  exact absurd (hC n) (by simpa using hn)

/-- Convergence, from an eventual bound on an arbitrary ultrafilter. -/
example (h : ∀ᶠ i in U, ‖f i‖ ≤ C) : Tendsto f U (𝓝 (U.ultralimit f)) :=
  tendsto_ultralimit_of_eventually_norm_le h

/-- **A negative bound is vacuous, not an error.** No side condition `0 ≤ C` appears, and
the statement below is provable precisely because its hypothesis cannot be met. -/
example (h : ∀ᶠ i in U, ‖f i‖ ≤ -1) : ‖U.ultralimit f‖ ≤ -1 :=
  norm_ultralimit_le h

/-- The hypothesis is membership of a large set, so a bound holding on *some* member of
the ultrafilter suffices — the family is unconstrained off it. -/
example (V : Ultrafilter ℕ) (g : ℕ → ℝ) (hV : {n : ℕ | ‖g n‖ ≤ 1} ∈ V) :
    ‖V.ultralimit g‖ ≤ 1 :=
  norm_ultralimit_le (eventually_of_mem hV fun _ hn ↦ hn)

/-- The order rules from the compact API remain available on `ℝ≥0∞` and are untouched;
this module adds real-valued entry conditions and changes nothing else. -/
example (h : ∀ᶠ i in U, ‖f i‖ ≤ C) : |U.ultralimit f| ≤ C :=
  abs_ultralimit_le h

end Tests

end Ultrafilter
