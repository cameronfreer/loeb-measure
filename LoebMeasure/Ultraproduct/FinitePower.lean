/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Filter.Germ.Basic

/-!
# Finite powers, coordinate splits, and permutations (D0.4 spike)

D0.4 spike (issue #4): audit the pinned-mathlib equivalences for finite powers,
reindexing, permutations, and coordinate splits, and establish that a single canonical
split family is usable with **explicit** measurable spaces.

## Audit outcome

Mathlib already supplies the split at the pinned revision:

* `Fin.appendEquiv m n : (Fin m → α) × (Fin n → α) ≃ (Fin (m + n) → α)`, built from
  `Fin.append`/`Fin.addCases`, with `@[simps]`-generated `apply`/`symm_apply` lemmas
  and the component rules `Fin.append_left`, `Fin.append_right`.

This is adopted as **the** canonical split; the project defines no competing
composite. What mathlib does *not* supply, and what this spike adds, is the
measurability layer against explicit measurable spaces, plus the reindexing and
permutation actions in the shape the graded API will use.

## Contents

* `Loeb.splitEquiv`: the project's canonical name for `Fin.appendEquiv`, so that a
  future change of canonical split is a one-line edit.
* `measurable_reindex`, `measurable_splitEquiv`, `measurable_splitEquiv_symm`,
  `measurable_permute`: measurability against a *supplied* `MeasurableSpace Ω`
  (never a global instance on the power type), the discipline the graded layer needs.
* `Loeb.permute` with `permute_one`, `permute_mul`, `permute_permute_symm`: the
  finite-permutation action and its functoriality.
* `MockGraded`: the deliberately minimal mock interface — measurable spaces as
  explicit data, `MeasurableSet[·]` statements — exercising a nontrivial coordinate
  split and a permutation. **Scope limit (per review):** the real
  `Graded.ProbabilitySpace` bundling decision is deferred to M6; this establishes only
  that the chosen equivalences are usable with explicit measurable spaces.

## Degree zero

`splitEquiv_zero_left`, `permute_zero`, and `mockSectionAt_zero` record that the
`n = 0` and `m = 0` cases are painless, as required by the architecture's public API
rules.

Declaration names are provisional; the M1 units U4/U5 promote this material.
-/

namespace Loeb

open MeasureTheory

variable {Ω : Type*} {m n : ℕ}

/-! ### The canonical split -/

/-- The canonical coordinate split, `(Fin m → Ω) × (Fin n → Ω) ≃ (Fin (m + n) → Ω)`.

This wraps `Fin.appendEquiv`. It is a `def`, not an `abbrev`, deliberately: an `abbrev`
is transparent and so would *not* insulate downstream code from a change of underlying
equivalence. The wrapper simp lemmas below are the intended interface, and graded laws
should use only them, so that changing the underlying split stays a change to this
file. -/
def splitEquiv (Ω : Type*) (m n : ℕ) :
    (Fin m → Ω) × (Fin n → Ω) ≃ (Fin (m + n) → Ω) :=
  Fin.appendEquiv m n

@[simp]
theorem splitEquiv_apply_castAdd (x : Fin m → Ω) (y : Fin n → Ω) (i : Fin m) :
    splitEquiv Ω m n (x, y) (Fin.castAdd n i) = x i :=
  Fin.append_left x y i

@[simp]
theorem splitEquiv_apply_natAdd (x : Fin m → Ω) (y : Fin n → Ω) (i : Fin n) :
    splitEquiv Ω m n (x, y) (Fin.natAdd m i) = y i :=
  Fin.append_right x y i

@[simp]
theorem splitEquiv_symm_apply_fst (f : Fin (m + n) → Ω) (i : Fin m) :
    ((splitEquiv Ω m n).symm f).1 i = f (Fin.castAdd n i) := rfl

@[simp]
theorem splitEquiv_symm_apply_snd (f : Fin (m + n) → Ω) (i : Fin n) :
    ((splitEquiv Ω m n).symm f).2 i = f (Fin.natAdd m i) := rfl

/-- Degree zero on the right is painless: splitting off no coordinates recovers the
original tuple. -/
theorem splitEquiv_zero_right (x : Fin m → Ω) (y : Fin 0 → Ω) (i : Fin m) :
    splitEquiv Ω m 0 (x, y) (Fin.castAdd 0 i) = x i :=
  Fin.append_left x y i

/-- Degree zero on the left: splitting off all coordinates recovers the original
tuple. -/
theorem splitEquiv_zero_left (x : Fin 0 → Ω) (y : Fin n → Ω) (i : Fin n) :
    splitEquiv Ω 0 n (x, y) (Fin.natAdd 0 i) = y i :=
  Fin.append_right x y i

/-! ### Reindexing and permutations -/

/-- Reindexing a finite power along a map of index types. -/
def reindex {κ κ' : Type*} (f : κ' → κ) (x : κ → Ω) : κ' → Ω := x ∘ f

@[simp]
theorem reindex_apply {κ κ' : Type*} (f : κ' → κ) (x : κ → Ω) (i : κ') :
    reindex f x i = x (f i) := rfl

@[simp]
theorem reindex_id {κ : Type*} (x : κ → Ω) : reindex id x = x := rfl

theorem reindex_comp {κ κ' κ'' : Type*} (f : κ' → κ) (g : κ'' → κ') (x : κ → Ω) :
    reindex g (reindex f x) = reindex (f ∘ g) x := rfl

/-- The action of a finite permutation on a finite power, by precomposition.

This is a **right** action: `permute` is contravariant, so `permute (σ * τ)` is
`permute τ ∘ permute σ` (see `permute_mul`), not the other way round. That is the
natural pullback convention for tuples, and it is what the graded permutation laws
will use; a conventional `MulAction` would instead precompose with `σ⁻¹`. Downstream
statements must not silently assume the covariant convention. -/
def permute (σ : Equiv.Perm (Fin n)) (x : Fin n → Ω) : Fin n → Ω := reindex σ x

@[simp]
theorem permute_apply (σ : Equiv.Perm (Fin n)) (x : Fin n → Ω) (i : Fin n) :
    permute σ x i = x (σ i) := rfl

@[simp]
theorem permute_one (x : Fin n → Ω) : permute (1 : Equiv.Perm (Fin n)) x = x := rfl

/-- Contravariance of the permutation action: the order of `σ` and `τ` swaps. -/
theorem permute_mul (σ τ : Equiv.Perm (Fin n)) (x : Fin n → Ω) :
    permute (σ * τ) x = permute τ (permute σ x) := rfl

@[simp]
theorem permute_permute_symm (σ : Equiv.Perm (Fin n)) (x : Fin n → Ω) :
    permute σ⁻¹ (permute σ x) = x := by
  funext i; simp

/-- Degree zero is painless: every permutation acts trivially. -/
@[simp]
theorem permute_zero (σ : Equiv.Perm (Fin 0)) (x : Fin 0 → Ω) : permute σ x = x := by
  funext i; exact absurd i.isLt (Nat.not_lt_zero _)

/-! ### Measurability for the standard pi spaces

**These are the easy case.** Every statement below takes the measurable space on `Ω` as
data, but the power spaces are then mathlib's inferred `MeasurableSpace.pi` instances.
That is *not* the same as an arbitrary supplied graded space: it is the concrete family
against which graded compatibility hypotheses get discharged.

The graded statements — `MockGraded.measurableSet_sectionAt` and
`MockGraded.measurableSet_permute_preimage` below — instead take the measurable spaces
at each degree as explicit data and carry the compatibility (measurability of the split
or the permutation) as a **hypothesis**, because in general several unrelated
measurable spaces on the same power type must coexist. The lemmas in this section are
what discharge those hypotheses for the pi family; see the `MockGraded.pi` examples. -/

section Measurable

variable [MeasurableSpace Ω]

theorem measurable_reindex {κ κ' : Type*} (f : κ' → κ) :
    Measurable (reindex (Ω := Ω) f) :=
  measurable_pi_lambda _ fun i ↦ measurable_pi_apply (f i)

theorem measurable_permute (σ : Equiv.Perm (Fin n)) :
    Measurable (permute (Ω := Ω) σ) :=
  measurable_reindex _

theorem measurable_splitEquiv :
    Measurable (splitEquiv Ω m n) :=
  measurable_pi_lambda _ fun i ↦ by
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · have h : (fun c : (Fin m → Ω) × (Fin n → Ω) ↦ splitEquiv Ω m n c (Fin.castAdd n j))
          = fun c ↦ c.1 j := funext fun c ↦ splitEquiv_apply_castAdd c.1 c.2 j
      rw [h]
      exact (measurable_pi_apply j).comp measurable_fst
    · have h : (fun c : (Fin m → Ω) × (Fin n → Ω) ↦ splitEquiv Ω m n c (Fin.natAdd m j))
          = fun c ↦ c.2 j := funext fun c ↦ splitEquiv_apply_natAdd c.1 c.2 j
      rw [h]
      exact (measurable_pi_apply j).comp measurable_snd

theorem measurable_splitEquiv_symm :
    Measurable (splitEquiv Ω m n).symm :=
  Measurable.prodMk (measurable_reindex _) (measurable_reindex _)

end Measurable

/-! ### Mock graded interface

A deliberately minimal stand-in: measurable spaces as explicit data indexed by degree,
with no measures, no compatibility fields, and no injection-category encoding. Its
only purpose is to show the canonical split and the permutation action work with
`MeasurableSet[·]` statements. The real bundling decision is deferred to M6. -/

/-- Mock graded family: one measurable space per degree, supplied as data. -/
structure MockGraded (Ω : Type*) where
  /-- The measurable space at degree `n`. -/
  mspace : ∀ n : ℕ, MeasurableSpace (Fin n → Ω)

namespace MockGraded

variable (G : MockGraded Ω)

/-- A section of a degree-`m + n` set at a degree-`m` point, along the canonical
split. Named `sectionAt` per the blueprint (`section` is a Lean keyword). -/
def sectionAt (s : Set (Fin (m + n) → Ω)) (x : Fin m → Ω) : Set (Fin n → Ω) :=
  {y | splitEquiv Ω m n (x, y) ∈ s}

@[simp]
theorem mem_sectionAt {s : Set (Fin (m + n) → Ω)} {x : Fin m → Ω} {y : Fin n → Ω} :
    y ∈ sectionAt (n := n) s x ↔ splitEquiv Ω m n (x, y) ∈ s := Iff.rfl

/-- Sections of a measurable set are measurable, stated against the *supplied*
measurable spaces at degrees `m + n` and `n`. This is the shape the graded Fubini
statement will take; note it never mentions a product sigma-algebra. -/
theorem measurableSet_sectionAt {s : Set (Fin (m + n) → Ω)}
    (hs : MeasurableSet[G.mspace (m + n)] s) (x : Fin m → Ω)
    (hsplit : Measurable[G.mspace n, G.mspace (m + n)] fun y ↦ splitEquiv Ω m n (x, y)) :
    MeasurableSet[G.mspace n] (sectionAt s x) :=
  hsplit hs

/-- Degree zero is painless: a section at the empty tuple is the whole set, transported
along the canonical split. -/
theorem sectionAt_zero (s : Set (Fin (0 + n) → Ω)) (x : Fin 0 → Ω) :
    sectionAt s x = (splitEquiv Ω 0 n) ∘ (fun y ↦ (x, y)) ⁻¹' s := rfl

/-- Permutation compatibility, stated against supplied measurable spaces: if the action
is measurable at degree `n`, permuted preimages of measurable sets are measurable. -/
theorem measurableSet_permute_preimage {s : Set (Fin n → Ω)}
    (hs : MeasurableSet[G.mspace n] s) (σ : Equiv.Perm (Fin n))
    (hperm : Measurable[G.mspace n, G.mspace n] (permute (Ω := Ω) σ)) :
    MeasurableSet[G.mspace n] (permute (Ω := Ω) σ ⁻¹' s) :=
  hperm hs

end MockGraded

/-- With the standard pi measurable spaces, the mock family's hypotheses are all
discharged by the measurability lemmas above: a coherent instance exists. -/
noncomputable def MockGraded.pi (Ω : Type*) [MeasurableSpace Ω] : MockGraded Ω where
  mspace _ := MeasurableSpace.pi

/-- Discharging the permutation hypothesis for the pi family. -/
example [MeasurableSpace Ω] (σ : Equiv.Perm (Fin n)) (s : Set (Fin n → Ω))
    (hs : MeasurableSet[(MockGraded.pi Ω).mspace n] s) :
    MeasurableSet[(MockGraded.pi Ω).mspace n] (permute (Ω := Ω) σ ⁻¹' s) :=
  (MockGraded.pi Ω).measurableSet_permute_preimage hs σ (measurable_permute σ)

/-- Discharging the *split* hypothesis for the pi family: the partially applied split
`fun y ↦ splitEquiv Ω m n (x, y)` is measurable, so sections of measurable sets are
measurable. This is the graded-shaped counterpart of the permutation example, and the
concrete evidence that `measurableSet_sectionAt`'s hypothesis is dischargeable rather
than vacuous. -/
example [MeasurableSpace Ω] (s : Set (Fin (m + n) → Ω))
    (hs : MeasurableSet[(MockGraded.pi Ω).mspace (m + n)] s) (x : Fin m → Ω) :
    MeasurableSet[(MockGraded.pi Ω).mspace n] (MockGraded.sectionAt s x) := by
  apply (MockGraded.pi Ω).measurableSet_sectionAt hs x
  exact measurable_splitEquiv.comp (measurable_const.prodMk measurable_id)

/-! ### Simp-behavior tests

D0.4 asks for *usable* simp behavior, not merely the existence of equivalences. These
examples are discharged by `simp` alone. -/

section SimpTests

/-- Coordinates of a split reduce on both sides. -/
example (x : Fin m → Ω) (y : Fin n → Ω) (i : Fin m) (j : Fin n) :
    splitEquiv Ω m n (x, y) (Fin.castAdd n i) = x i ∧
      splitEquiv Ω m n (x, y) (Fin.natAdd m j) = y j := by
  simp

/-- The split round-trips: `symm` after `apply` is the identity. -/
example (x : Fin m → Ω) (y : Fin n → Ω) :
    (splitEquiv Ω m n).symm (splitEquiv Ω m n (x, y)) = (x, y) := by
  simp

/-- Degree zero: an empty tuple is unique, so a `Fin 0` component is inert. -/
example (x : Fin 0 → Ω) (y : Fin n → Ω) :
    (splitEquiv Ω 0 n).symm (splitEquiv Ω 0 n (x, y)) = (x, y) := by
  simp

/-- Degree zero: permutations act trivially. -/
example (σ : Equiv.Perm (Fin 0)) (x : Fin 0 → Ω) : permute σ x = x := by
  simp

/-- The permutation action cancels inverses and fixes the identity. Composition is
*not* in this list: `permute_mul` is contravariant and is stated as a theorem, not a
simp lemma, precisely so that rewriting does not silently pick an orientation. -/
example (σ : Equiv.Perm (Fin n)) (x : Fin n → Ω) :
    permute σ⁻¹ (permute σ x) = x ∧ permute (1 : Equiv.Perm (Fin n)) x = x := by
  simp

/-- Composition, stated explicitly in its contravariant form. -/
example (σ τ : Equiv.Perm (Fin n)) (x : Fin n → Ω) :
    permute (σ * τ) x = permute τ (permute σ x) :=
  permute_mul σ τ x

/-- Reindexing composes with coordinate evaluation. -/
example {κ κ' : Type*} (f : κ' → κ) (x : κ → Ω) (i : κ') : reindex f x i = x (f i) := by
  simp

end SimpTests

/-! ### U4: the ultraproduct equivalences this audit does *not* supply

Everything above concerns plain finite powers `Fin n → Ω`. The ultraproduct
equivalences remain U4 work and are **not** discharged by this spike; their type shapes
are recorded here so the U4 issue can name them precisely.

Constructing them is genuine work: the forward maps are easy (push a germ of functions
to a function of germs, coordinatewise), but the inverses need finiteness of the index
type in order to combine finitely many representatives over a finite intersection of
eventual-equality sets. -/

section U4Shapes

variable {ι : Type*}

open Filter

/-- Intended shape of `Filter.Product.finitePiEquiv` (U4): a filter product of finite
function types is a finite function type of filter products. Requires `[Finite κ]` to
construct. -/
abbrev FinitePiEquivShape (l : Filter ι) (X : ι → Type*) (κ : Type*) : Type _ :=
  (l.Product fun i ↦ (κ → X i)) ≃ (κ → l.Product X)

/-- Intended shape of `Filter.Product.finPowerEquiv` (U4): the `Fin`-indexed case,
which is the one the graded layer uses. -/
abbrev FinPowerEquivShape (l : Filter ι) (X : ι → Type*) (k : ℕ) : Type _ :=
  (l.Product fun i ↦ (Fin k → X i)) ≃ (Fin k → l.Product X)

/-- Both shapes elaborate, and the `Fin` case is the `κ := Fin k` instance of the
general one. -/
example (l : Filter ι) (X : ι → Type*) (k : ℕ) :
    FinPowerEquivShape l X k = FinitePiEquivShape l X (Fin k) := rfl

end U4Shapes

/-!
Beyond constructing the two equivalences above, U4/U5 must also supply their
interaction with this file's API, none of which is proved here:

* evaluation: `finPowerEquiv` commutes with coordinate evaluation, i.e. the germ of the
  `j`-th coordinate is the `j`-th coordinate of the transported tuple;
* naturality in the stagewise maps (compatibility with `Filter.Product.map`);
* compatibility with `splitEquiv`: transporting a stagewise split along
  `finPowerEquiv` agrees with splitting the transported tuple;
* compatibility with `reindex` and `permute`: a stagewise reindexing transports to the
  reindexing of the transported tuple, and likewise for permutations — with the
  contravariance convention of `permute_mul` preserved;
* the degree-zero and degree-one cases, matching the painless-`n = 0` rule.

Measure theory is then done on the `l.Product (fun i ↦ Fin k → X i)` side, where sets
are internal, and transported to `Fin k → l.Product X` only at API boundaries.
-/

end Loeb
