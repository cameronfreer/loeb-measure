/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.Set
import LoebMeasure.Ultraproduct.Prod

/-!
# Boolean operations on internal sets

Internal sets carry the stagewise Boolean operations, and `carrier` preserves them.

## Where each fact's structure comes from

The operations are `Filter.Product.map`/`map₂` of the corresponding `Set` operations,
and the `BooleanAlgebra` instance is built from their stagewise laws through
`Lattice.mk'` and `DistribLattice.ofInfSupLe`. All of that uses only ordinary `Filter`
API — no ultrafilter property, no nonempty fibers, no countable incompleteness. The
public instance is scoped to `InternalSet U X` rather than installed on
`Filter.Product`, since a generic public instance is a broader upstream decision with
coherence implications (see #45).

The order is eventual stagewise inclusion (`le_ofFun_iff`).

That filter-genericity is **verified by compilation**, not asserted: the
`ArbitraryFilter` section below rebuilds the entire construction over an arbitrary
`l : Filter ι` with `local instance`s, so nothing escapes onto `Filter.Product` and no
diamond can reach `InternalSet`. The check has teeth — `Ultrafilter.eventually_or`,
which `carrier_sup` needs, does not typecheck at a general filter — so a step that
secretly required the ultrafilter would break that section.

The theorems saying `carrier` *preserves* the operations are where the structure
stratifies, and the pattern is not uniform:

| Fact | Consumes |
| --- | --- |
| `carrier_bot` | properness — supplied by `Ultrafilter` |
| `carrier_top`, `carrier_inf` | ordinary filter laws only |
| `carrier_sup`, `carrier_compl` | the **ultrafilter dichotomy** |
| `carrier_sdiff` | derived: `sdiff_eq` then `carrier_inf`/`carrier_compl` |
| `carrier_symmDiff` | derived: `carrier_sup` and `carrier_sdiff` |

Nothing here uses nonempty fibers or countable incompleteness, and **`carrier_injective`
is deliberately not used**: set-ring closure needs only that representing internal sets
*exist*. Proving these laws through injectivity would drag its nonempty-fibers
hypothesis into statements that hold for arbitrary fibers. Injectivity becomes
load-bearing later, at content transport.
-/

namespace Loeb.InternalSet

open Filter

variable {ι : Type*} {U : Ultrafilter ι} {X : ι → Type*}

/-! ### Operations -/

instance : Bot (InternalSet U X) := ⟨Filter.Product.ofFun fun _ ↦ ∅⟩
instance : Top (InternalSet U X) := ⟨Filter.Product.ofFun fun _ ↦ Set.univ⟩
instance : Compl (InternalSet U X) := ⟨Filter.Product.map fun _ ↦ compl⟩
instance : Max (InternalSet U X) := ⟨Filter.Product.map₂ fun _ ↦ (· ∪ ·)⟩
instance : Min (InternalSet U X) := ⟨Filter.Product.map₂ fun _ ↦ (· ∩ ·)⟩
instance : SDiff (InternalSet U X) := ⟨Filter.Product.map₂ fun _ ↦ (· \ ·)⟩

@[simp] theorem bot_def : (⊥ : InternalSet U X) = Filter.Product.ofFun fun _ ↦ ∅ := rfl
@[simp] theorem top_def :
    (⊤ : InternalSet U X) = Filter.Product.ofFun fun _ ↦ Set.univ := rfl

@[simp]
theorem compl_ofFun (A : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun A : InternalSet U X)ᶜ = Filter.Product.ofFun fun i ↦ (A i)ᶜ :=
  rfl

@[simp]
theorem sup_ofFun (A B : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun A : InternalSet U X) ⊔ Filter.Product.ofFun B
      = Filter.Product.ofFun fun i ↦ A i ∪ B i :=
  rfl

@[simp]
theorem inf_ofFun (A B : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun A : InternalSet U X) ⊓ Filter.Product.ofFun B
      = Filter.Product.ofFun fun i ↦ A i ∩ B i :=
  rfl

@[simp]
theorem sdiff_ofFun (A B : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun A : InternalSet U X) \ Filter.Product.ofFun B
      = Filter.Product.ofFun fun i ↦ A i \ B i :=
  rfl

/-! ### The Boolean algebra

Each law is the corresponding `Set` law applied stagewise, so the construction uses
only ordinary `Filter` API — no ultrafilter property. The public instance is scoped to
`InternalSet U X`; a generic instance on `Filter.Product` is a broader upstream
decision and is deliberately out of scope. -/

private theorem ofFun_congrArg {A B : (i : ι) → Set (X i)} (h : ∀ i, A i = B i) :
    (Filter.Product.ofFun A : InternalSet U X) = Filter.Product.ofFun B :=
  congrArg _ (funext h)

instance instLattice : Lattice (InternalSet U X) :=
  Lattice.mk'
    (sup_comm := by
      intro A B
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' => exact ofFun_congrArg fun i ↦ Set.union_comm _ _)
    (sup_assoc := by
      intro A B C
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' =>
        induction C using Filter.Product.inductionOn with
        | _ C' => exact ofFun_congrArg fun i ↦ Set.union_assoc _ _ _)
    (inf_comm := by
      intro A B
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' => exact ofFun_congrArg fun i ↦ Set.inter_comm _ _)
    (inf_assoc := by
      intro A B C
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' =>
        induction C using Filter.Product.inductionOn with
        | _ C' => exact ofFun_congrArg fun i ↦ Set.inter_assoc _ _ _)
    (sup_inf_self := by
      intro A B
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' => exact ofFun_congrArg fun i ↦ sup_inf_self)
    (inf_sup_self := by
      intro A B
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' => exact ofFun_congrArg fun i ↦ inf_sup_self)

instance instDistribLattice : DistribLattice (InternalSet U X) :=
  DistribLattice.ofInfSupLe fun A B C ↦ by
    induction A, B using Filter.Product.inductionOn₂ with
    | _ A' B' =>
      induction C using Filter.Product.inductionOn with
      | _ C' => exact le_of_eq (ofFun_congrArg fun i ↦ Set.inter_union_distrib_left ..)

instance instBooleanAlgebra : BooleanAlgebra (InternalSet U X) where
  inf_compl_le_bot A := by
    induction A using Filter.Product.inductionOn with
    | _ A' => exact le_of_eq (ofFun_congrArg fun i ↦ Set.inter_compl_self _)
  top_le_sup_compl A := by
    induction A using Filter.Product.inductionOn with
    | _ A' => exact le_of_eq (ofFun_congrArg fun i ↦ (Set.union_compl_self _).symm)
  le_top A := by
    induction A using Filter.Product.inductionOn with
    | _ A' => exact sup_eq_right.1 (ofFun_congrArg fun i ↦ Set.union_univ _)
  bot_le A := by
    induction A using Filter.Product.inductionOn with
    | _ A' => exact sup_eq_right.1 (ofFun_congrArg fun i ↦ Set.empty_union _)
  sdiff_eq A B := by
    induction A, B using Filter.Product.inductionOn₂ with
    | _ A' B' => exact ofFun_congrArg fun i ↦ Set.sdiff_eq _ _

/-- The order is eventual stagewise inclusion. -/
@[simp]
theorem le_ofFun_iff (A B : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun A : InternalSet U X) ≤ Filter.Product.ofFun B ↔
      ∀ᶠ i in (U : Filter ι), A i ⊆ B i := by
  rw [← sup_eq_right]
  simp only [sup_ofFun, Filter.Product.ofFun_eq_ofFun]
  exact eventually_congr (Eventually.of_forall fun i ↦ Set.union_eq_right)

/-- **Carriers are monotone.** Ordinary filter laws only.

Worth stating separately rather than deriving from `carrier_sup`: that route would go
through `sup_eq_right` and so inherit the **ultrafilter dichotomy**, which monotonicity
does not need. Both eventual statements are simply intersected. -/
@[gcongr]
theorem carrier_mono {A B : InternalSet U X} (h : A ≤ B) : carrier A ⊆ carrier B := by
  induction A, B using Filter.Product.inductionOn₂ with
  | _ A' B' =>
    rw [le_ofFun_iff] at h
    intro x hx
    induction x using Filter.Product.inductionOn with
    | _ x' => exact ((mem_carrier_ofFun x' A').1 hx).mp (h.mono fun _ hsub hmem ↦ hsub hmem)

/-! ### Carriers of the operations

This is where the ultrafilter structure enters, and only here. Each statement records
what it consumes. -/

/-- The empty internal set has empty carrier. Uses **properness** — a point of the
carrier would make `∅` eventually inhabited — which `Ultrafilter` supplies. -/
@[simp]
theorem carrier_bot : carrier (⊥ : InternalSet U X) = ∅ := by
  ext x
  induction x using Filter.Product.inductionOn with
  | _ x' =>
    simp only [bot_def, mem_carrier_ofFun, Set.mem_empty_iff_false, iff_false]
    exact fun h ↦ h.exists.elim fun _ hi ↦ hi

/-- The full internal set has full carrier. Ordinary filter laws only. -/
@[simp]
theorem carrier_top : carrier (⊤ : InternalSet U X) = Set.univ := by
  ext x
  induction x using Filter.Product.inductionOn with
  | _ x' => simp

/-- Intersection is preserved. Ordinary filter laws only: `∀ᶠ` distributes over `∧`. -/
@[simp]
theorem carrier_inf (A B : InternalSet U X) :
    carrier (A ⊓ B) = carrier A ∩ carrier B := by
  ext x
  induction x, A using Filter.Product.inductionOn₂ with
  | _ x' A' =>
    induction B using Filter.Product.inductionOn with
    | _ B' => simp [Filter.eventually_and]

/-- Union is preserved. Uses the **ultrafilter dichotomy**: an eventual disjunction
splits into a disjunction of eventual statements, which is false for a general
filter. -/
@[simp]
theorem carrier_sup (A B : InternalSet U X) :
    carrier (A ⊔ B) = carrier A ∪ carrier B := by
  ext x
  induction x, A using Filter.Product.inductionOn₂ with
  | _ x' A' =>
    induction B using Filter.Product.inductionOn with
    | _ B' => simpa using Ultrafilter.eventually_or

/-- Complement is preserved. Uses the **ultrafilter dichotomy** via
`Ultrafilter.eventually_not`. -/
@[simp]
theorem carrier_compl (A : InternalSet U X) : carrier Aᶜ = (carrier A)ᶜ := by
  ext x
  induction x, A using Filter.Product.inductionOn₂ with
  | _ x' A' =>
    simp only [compl_ofFun, mem_carrier_ofFun, Set.mem_compl_iff]
    exact Ultrafilter.eventually_not

/-- Difference is preserved. Genuinely *derived*, as the table says: `sdiff_eq` reduces
it to intersection with a complement, and those two laws finish it. -/
@[simp]
theorem carrier_sdiff (A B : InternalSet U X) :
    carrier (A \ B) = carrier A \ carrier B := by
  rw [sdiff_eq, carrier_inf, carrier_compl, Set.sdiff_eq]

/-- Symmetric difference is preserved, derived from supremum and difference. This is
the operation M3's internal-approximation arguments are stated with.

The final `rfl` bridges `∪` and `⊔` on `Set`, which are definitionally but not
syntactically equal. -/
@[simp]
theorem carrier_symmDiff (A B : InternalSet U X) :
    carrier (symmDiff A B) = symmDiff (carrier A) (carrier B) := by
  rw [symmDiff_def, symmDiff_def, carrier_sup, carrier_sdiff, carrier_sdiff]; rfl

/-! ### The arbitrary-filter check

The claim above — that the construction uses only ordinary `Filter` API — is verified
here rather than asserted: the whole development is rebuilt over an arbitrary
`l : Filter ι`, with `local instance`s so that nothing is installed on `Filter.Product`
outside this section and no diamond can reach `InternalSet`. If any step secretly
needed the ultrafilter, this section would fail to elaborate. -/

section ArbitraryFilter

variable {l : Filter ι}

local instance : Bot (l.Product fun i ↦ Set (X i)) := ⟨Filter.Product.ofFun fun _ ↦ ∅⟩
local instance : Top (l.Product fun i ↦ Set (X i)) :=
  ⟨Filter.Product.ofFun fun _ ↦ Set.univ⟩
local instance : Compl (l.Product fun i ↦ Set (X i)) :=
  ⟨Filter.Product.map fun _ ↦ compl⟩
local instance : Max (l.Product fun i ↦ Set (X i)) :=
  ⟨Filter.Product.map₂ fun _ ↦ (· ∪ ·)⟩
local instance : Min (l.Product fun i ↦ Set (X i)) :=
  ⟨Filter.Product.map₂ fun _ ↦ (· ∩ ·)⟩
local instance : SDiff (l.Product fun i ↦ Set (X i)) :=
  ⟨Filter.Product.map₂ fun _ ↦ (· \ ·)⟩

private theorem generic_congrArg {A B : (i : ι) → Set (X i)} (h : ∀ i, A i = B i) :
    (Filter.Product.ofFun A : l.Product fun i ↦ Set (X i)) = Filter.Product.ofFun B :=
  congrArg _ (funext h)

local instance genericLattice : Lattice (l.Product fun i ↦ Set (X i)) :=
  Lattice.mk'
    (sup_comm := by
      intro A B
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' => exact generic_congrArg fun i ↦ Set.union_comm _ _)
    (sup_assoc := by
      intro A B C
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' =>
        induction C using Filter.Product.inductionOn with
        | _ C' => exact generic_congrArg fun i ↦ Set.union_assoc _ _ _)
    (inf_comm := by
      intro A B
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' => exact generic_congrArg fun i ↦ Set.inter_comm _ _)
    (inf_assoc := by
      intro A B C
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' =>
        induction C using Filter.Product.inductionOn with
        | _ C' => exact generic_congrArg fun i ↦ Set.inter_assoc _ _ _)
    (sup_inf_self := by
      intro A B
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' => exact generic_congrArg fun i ↦ sup_inf_self)
    (inf_sup_self := by
      intro A B
      induction A, B using Filter.Product.inductionOn₂ with
      | _ A' B' => exact generic_congrArg fun i ↦ inf_sup_self)

local instance genericDistribLattice : DistribLattice (l.Product fun i ↦ Set (X i)) :=
  DistribLattice.ofInfSupLe fun A B C ↦ by
    induction A, B using Filter.Product.inductionOn₂ with
    | _ A' B' =>
      induction C using Filter.Product.inductionOn with
      | _ C' => exact le_of_eq (generic_congrArg fun i ↦ Set.inter_union_distrib_left ..)

/-- **The verification.** A `BooleanAlgebra` over an arbitrary filter, using no
ultrafilter property anywhere. The public instance above is this construction at
`l := (U : Filter ι)`. -/
local instance genericBooleanAlgebra :
    BooleanAlgebra (l.Product fun i ↦ Set (X i)) where
  inf_compl_le_bot A := by
    induction A using Filter.Product.inductionOn with
    | _ A' => exact le_of_eq (generic_congrArg fun i ↦ Set.inter_compl_self _)
  top_le_sup_compl A := by
    induction A using Filter.Product.inductionOn with
    | _ A' => exact le_of_eq (generic_congrArg fun i ↦ (Set.union_compl_self _).symm)
  le_top A := by
    induction A using Filter.Product.inductionOn with
    | _ A' => exact sup_eq_right.1 (generic_congrArg fun i ↦ Set.union_univ _)
  bot_le A := by
    induction A using Filter.Product.inductionOn with
    | _ A' => exact sup_eq_right.1 (generic_congrArg fun i ↦ Set.empty_union _)
  sdiff_eq A B := by
    induction A, B using Filter.Product.inductionOn₂ with
    | _ A' B' => exact generic_congrArg fun i ↦ Set.sdiff_eq _ _

end ArbitraryFilter

/-! ### API tests -/

section Tests

/-- **The headline capability**: internal sets *are* a Boolean algebra. Compilation of
the operations alone does not establish this — an earlier revision defined every
operation and had no instance — so it is tested directly. -/
example : BooleanAlgebra (InternalSet U X) := inferInstance

/-- And the instance supports Boolean reasoning, not merely synthesis. -/
example (A B : InternalSet U X) : (A ⊓ B)ᶜ = Aᶜ ⊔ Bᶜ := compl_inf

example (A : InternalSet U X) : A ⊓ Aᶜ = ⊥ := inf_compl_self A

example (A B C : InternalSet U X) : A ⊓ (B ⊔ C) = A ⊓ B ⊔ A ⊓ C := inf_sup_left A B C

/-- The order is eventual stagewise inclusion. -/
example (A B : (i : ι) → Set (X i)) (h : ∀ᶠ i in (U : Filter ι), A i ⊆ B i) :
    (Filter.Product.ofFun A : InternalSet U X) ≤ Filter.Product.ofFun B :=
  (le_ofFun_iff A B).2 h

/-- Symmetric difference is preserved — the operation M3's approximation arguments use. -/
example (A B : InternalSet U X) :
    carrier (symmDiff A B) = symmDiff (carrier A) (carrier B) :=
  carrier_symmDiff A B

/-- Operations compute on representatives. -/
example (A B : (i : ι) → Set (X i)) :
    (Filter.Product.ofFun A : InternalSet U X) ⊔ Filter.Product.ofFun B
      = Filter.Product.ofFun fun i ↦ A i ∪ B i := by
  simp

/-- The carrier laws fire by `simp`, so downstream reasoning happens in ordinary set
language. -/
example (A B : InternalSet U X) :
    carrier (A ⊓ B) ∪ carrier (A \ B) = (carrier A ∩ carrier B) ∪ (carrier A \ carrier B) := by
  simp

/-- **A genuinely dependent family.** -/
example (U : Ultrafilter ℕ) (A B : (i : ℕ) → Set (Fin (i + 1))) :
    carrier ((Filter.Product.ofFun A : InternalSet U fun i ↦ Fin (i + 1))
        ⊔ Filter.Product.ofFun B)
      = carrier (Filter.Product.ofFun A : InternalSet U fun i ↦ Fin (i + 1))
        ∪ carrier (Filter.Product.ofFun B) :=
  carrier_sup _ _

end Tests

end Loeb.InternalSet
