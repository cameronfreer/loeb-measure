/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Finite

/-!
# Countable incompleteness and the diagonal lemma

The exact hypothesis behind Loeb-measure diagonalization, and the content-free diagonal
lemma itself. Accepted as ADR-0001 after the D0.1 spike (#1); the **proofs** are
promoted unchanged, while the prose below was corrected on the way in.

* `Filter.CountablyIncomplete`: some countable family of members has empty
  intersection. This is ADR-0001's accepted choice — its option 3, refined to the
  `Filter` level — and not a claim to be weakest among the candidates, since option 4
  was broader and incomparable. What it buys concretely: the diagonal lemma below needs
  only a filter carrying such a witness, not an ultrafilter, not `ℕ`-indexing, and not
  `Filter.hyperfilter` specifically.
* `Filter.countablyIncomplete_of_le_cofinite`: on a countable index type, any filter
  at least as fine as `cofinite` qualifies. In particular every nonprincipal
  ultrafilter on `ℕ` qualifies, and `Filter.hyperfilter_countablyIncomplete` records
  the canonical instance required by the ADR.
* `Filter.CountablyIncomplete.exists_forall_eventually_mem`: the content-free
  countable diagonalization. Given a stagewise family `A : ℕ → ∀ i, Set (X i)` that is
  eventually decreasing and eventually nonempty at every level, there is a single
  choice function `x` lying eventually in every level. In M2 language the conclusion
  is exactly `[x] ∈ carrier (A k)` for every `k`, but the statement here is
  deliberately quotient-free and content-free.

Nonempty fibers are assumed only to produce a value at the indices outside the good
set, where it is irrelevant — a stagewise *witness or default*, not a quotient
representative, which needs no such hypothesis.

The three hypotheses stay deliberately separate, per ADR-0001: carrier injectivity uses
the ultrafilter dichotomy and nonempty fibers but **no** incompleteness, while the
selection theorem below uses incompleteness and nonempty fibers but **no** ultrafilter
property. Nothing here mentions `InternalSet`, quotients, or measure theory.

This material is a mathlib upstream candidate but is deliberately **not** under
`LoebMeasure/Mathlib/`: #12 records that its name and its properness convention are
unsettled, and that directory holds only declarations whose upstream shape is decided.
#12 asks for downstream consumers before freezing those choices; defining the API here
is not itself a use of it, so that condition is still open.
-/

open Set

namespace Filter

variable {ι : Type*}

/-- A filter is *countably incomplete* if some countable family of its members has
empty intersection. This is the exact hypothesis consumed by Loeb-measure
diagonalization. -/
def CountablyIncomplete (F : Filter ι) : Prop :=
  ∃ I : ℕ → Set ι, (∀ k, I k ∈ F) ∧ ⋂ k, I k = ∅

/-- The witness family of a countably incomplete filter can be taken antitone. -/
theorem CountablyIncomplete.exists_antitone {F : Filter ι} (h : F.CountablyIncomplete) :
    ∃ J : ℕ → Set ι, Antitone J ∧ (∀ k, J k ∈ F) ∧ ⋂ k, J k = ∅ := by
  obtain ⟨I, hmem, hempty⟩ := h
  refine ⟨fun k ↦ ⋂ j ∈ Finset.range (k + 1), I j, fun a b hab x hx ↦
    mem_iInter₂.2 fun j hj ↦ mem_iInter₂.1 hx j
      (Finset.mem_range.2 ((Finset.mem_range.1 hj).trans_le (by omega))), fun k ↦
    (Filter.biInter_finset_mem _).2 fun j _ ↦ hmem j, ?_⟩
  rw [← subset_empty_iff, ← hempty]
  exact fun x hx ↦ mem_iInter.2 fun n ↦
    mem_iInter₂.1 (mem_iInter.1 hx n) n (Finset.mem_range.2 (Nat.lt_succ_self n))

/-- On a countable index type, every filter at least as fine as the cofinite filter is
countably incomplete. In particular every nonprincipal ultrafilter on `ℕ` is. -/
theorem countablyIncomplete_of_le_cofinite [Countable ι] {F : Filter ι}
    (hF : F ≤ cofinite) : F.CountablyIncomplete := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun _ ↦ univ, fun _ ↦ univ_mem, by
      rw [iInter_const]; exact univ_eq_empty_iff.2 hι⟩
  · obtain ⟨e, he⟩ := exists_surjective_nat ι
    refine ⟨fun k ↦ (e '' ↑(Finset.range (k + 1)))ᶜ, fun k ↦
      hF (((Finset.range (k + 1)).finite_toSet.image e).compl_mem_cofinite), ?_⟩
    rw [eq_empty_iff_forall_notMem]
    intro i hi
    obtain ⟨n, rfl⟩ := he i
    exact mem_iInter.1 hi n ⟨n, by simp, rfl⟩

/-- The canonical free ultrafilter on `ℕ` is countably incomplete: the hypothesis
required by ADR-0001 is satisfied by `Filter.hyperfilter ℕ`. -/
theorem hyperfilter_countablyIncomplete :
    (hyperfilter ℕ : Filter ℕ).CountablyIncomplete :=
  countablyIncomplete_of_le_cofinite hyperfilter_le_cofinite

section Diagonal

variable {F : Filter ι} {X : ι → Type*}

/-- Chain descent: a finitely-many-steps decreasing chain contains its later terms in
its earlier ones. -/
private theorem subset_of_chain {α : Type*} {B : ℕ → Set α} :
    ∀ {d : ℕ}, (∀ j < d, B (j + 1) ⊆ B j) → ∀ {k : ℕ}, k ≤ d → B d ⊆ B k := by
  intro d
  induction d with
  | zero => intro _ k hk; rw [Nat.le_zero.1 hk]
  | succ d ih =>
    intro h k hk
    rcases Nat.eq_or_lt_of_le hk with rfl | hk'
    · exact subset_rfl
    · exact (h d (Nat.lt_succ_self d)).trans
        (ih (fun j hj ↦ h j (hj.trans (Nat.lt_succ_self d))) (Nat.lt_succ_iff.1 hk'))

/-- **Countable diagonalization.** Along a countably incomplete filter, a stagewise
family of sets that is eventually decreasing and eventually nonempty at every level
admits a single choice function lying eventually in every level.

This is the content-free form of the Loeb saturation lemma: the conclusion
`∀ᶠ i in F, x i ∈ A k i` is, in M2 language, exactly `[x] ∈ carrier (A k)`. Only the
filter structure and the incompleteness witness are used — no ultrafilter property,
no measure, and no quotients. -/
theorem CountablyIncomplete.exists_forall_eventually_mem
    (hF : F.CountablyIncomplete) [∀ i, Nonempty (X i)] {A : ℕ → ∀ i, Set (X i)}
    (hdec : ∀ k, ∀ᶠ i in F, A (k + 1) i ⊆ A k i)
    (hne : ∀ k, ∀ᶠ i in F, (A k i).Nonempty) :
    ∃ x : ∀ i, X i, ∀ k, ∀ᶠ i in F, x i ∈ A k i := by
  classical
  obtain ⟨J, hJanti, hJmem, hJempty⟩ := hF.exists_antitone
  -- The "good" index sets: the incompleteness witness intersected with the sets where
  -- the chain conditions and nonemptiness hold up to level `k`.
  set S : ℕ → Set ι := fun k ↦
    J k ∩ {i | ∀ j < k, A (j + 1) i ⊆ A j i} ∩ {i | ∀ j ≤ k, (A j i).Nonempty} with hSdef
  have hSmem : ∀ k, S k ∈ F := by
    intro k
    have h1 : ∀ᶠ i in F, ∀ j < k, A (j + 1) i ⊆ A j i := by
      have := (eventually_all_finset (Finset.range k)).2 fun j _ ↦ hdec j
      exact this.mono fun i hi j hj ↦ hi j (Finset.mem_range.2 hj)
    have h2 : ∀ᶠ i in F, ∀ j ≤ k, (A j i).Nonempty := by
      have := (eventually_all_finset (Finset.range (k + 1))).2 fun j _ ↦ hne j
      exact this.mono fun i hi j hj ↦ hi j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    exact inter_mem (inter_mem (hJmem k) h1) h2
  have hSanti : Antitone S := by
    intro a b hab
    refine inter_subset_inter (inter_subset_inter (hJanti hab) ?_) ?_
    · exact fun i hi j hj ↦ hi j (lt_of_lt_of_le hj hab)
    · exact fun i hi j hj ↦ hi j (hj.trans hab)
  have hSempty : ⋂ k, S k = ∅ :=
    subset_empty_iff.1 ((iInter_mono fun k ↦ inter_subset_left.trans inter_subset_left).trans
      hJempty.subset)
  -- Per index, pick a point that lies in every level whose good set contains the index.
  have hpick : ∀ i, ∃ x : X i, ∀ k, i ∈ S k → x ∈ A k i := by
    intro i
    by_cases h0 : i ∈ S 0
    · have hex : ∃ k, i ∉ S k := by
        by_contra hcon
        exact absurd (mem_iInter.2 (not_exists_not.1 hcon)) (by simp [hSempty])
      set N := Nat.find hex with hNdef
      have hN : i ∉ S N := Nat.find_spec hex
      have hNpos : 0 < N := Nat.pos_of_ne_zero fun h ↦ hN (h ▸ h0)
      have hdmem : i ∈ S (N - 1) := not_not.1 (Nat.find_min hex (Nat.sub_lt hNpos one_pos))
      obtain ⟨⟨-, hchain⟩, hnonemp⟩ := hdmem
      obtain ⟨x, hx⟩ := hnonemp (N - 1) le_rfl
      refine ⟨x, fun k hk ↦ ?_⟩
      have hkd : k ≤ N - 1 := by
        by_contra hgt
        exact hN (hSanti (by omega) hk)
      exact subset_of_chain (B := fun j ↦ A j i) hchain hkd hx
    · exact ⟨Classical.arbitrary _, fun k hk ↦ absurd (hSanti (Nat.zero_le k) hk) h0⟩
  choose x hx using hpick
  exact ⟨x, fun k ↦ eventually_iff.2 (mem_of_superset (hSmem k) fun i hi ↦ hx i k hi)⟩

/-- The decreasing-intersection form: along a countably incomplete filter, a stagewise
decreasing family of eventually nonempty levels has a common eventual member. Stated
separately because downstream proofs sometimes have genuinely pointwise-decreasing
representatives. -/
theorem CountablyIncomplete.exists_forall_eventually_mem_of_antitone
    (hF : F.CountablyIncomplete) [∀ i, Nonempty (X i)] {A : ℕ → ∀ i, Set (X i)}
    (hdec : ∀ i, Antitone fun k ↦ A k i) (hne : ∀ k, ∀ᶠ i in F, (A k i).Nonempty) :
    ∃ x : ∀ i, X i, ∀ k, ∀ᶠ i in F, x i ∈ A k i :=
  hF.exists_forall_eventually_mem
    (fun k ↦ Eventually.of_forall fun i ↦ hdec i (Nat.le_succ k)) hne

end Diagonal

end Filter
