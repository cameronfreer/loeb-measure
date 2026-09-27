/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The canonical coordinate split and sections of tuple sets

The single canonical split of a finite power, fixed by the D0.4 audit:

```
Loeb.splitEquiv Ω m n : (Fin m → Ω) × (Fin n → Ω) ≃ (Fin (m + n) → Ω)
```

It wraps mathlib's `Fin.appendEquiv`, and it is an opaque `def` rather than an `abbrev`
so that downstream code depends on the wrapper simp rules below — forward in
`Fin.castAdd`/`Fin.natAdd` form, and both components of the inverse — rather than on the
underlying equivalence. Graded laws use only these rules; nothing downstream unfolds
`Fin.appendEquiv`. Round-trips are the generic `Equiv.symm_apply_apply` and
`Equiv.apply_symm_apply`, and close by bare `simp`.

The section of a set of `(m + n)`-tuples at an `m`-tuple is then purely algebraic:

```
sectionAt s x = {y | splitEquiv Ω m n (x, y) ∈ s}
```

Combined tuples become pairs through `(splitEquiv Ω m n).symm`; the orientation is the
one recorded in ADR-0005.

This module is measure-free and knows nothing of ultraproducts. The compatibility of the
split with the realization of stage powers lives in `LoebMeasure/Graded/Section.lean`,
where it is proved through M1's coordinate API.
-/

namespace Loeb

variable {Ω : Type*} {m n : ℕ}

/-! ### The canonical split -/

/-- **The canonical coordinate split**, `(Fin m → Ω) × (Fin n → Ω) ≃ (Fin (m + n) → Ω)`.

A `def`, not an `abbrev`, deliberately: an `abbrev` is transparent and so would not
insulate downstream code from a change of underlying equivalence. The wrapper simp rules
are the intended interface. -/
def splitEquiv (Ω : Type*) (m n : ℕ) : (Fin m → Ω) × (Fin n → Ω) ≃ (Fin (m + n) → Ω) :=
  Fin.appendEquiv m n

/-- The left block of a combined tuple. -/
@[simp]
theorem splitEquiv_apply_castAdd (x : Fin m → Ω) (y : Fin n → Ω) (i : Fin m) :
    splitEquiv Ω m n (x, y) (Fin.castAdd n i) = x i :=
  Fin.append_left x y i

/-- The right block of a combined tuple. -/
@[simp]
theorem splitEquiv_apply_natAdd (x : Fin m → Ω) (y : Fin n → Ω) (i : Fin n) :
    splitEquiv Ω m n (x, y) (Fin.natAdd m i) = y i :=
  Fin.append_right x y i

/-- The first component of a split tuple. -/
@[simp]
theorem splitEquiv_symm_apply_fst (f : Fin (m + n) → Ω) (i : Fin m) :
    ((splitEquiv Ω m n).symm f).1 i = f (Fin.castAdd n i) :=
  rfl

/-- The second component of a split tuple. -/
@[simp]
theorem splitEquiv_symm_apply_snd (f : Fin (m + n) → Ω) (i : Fin n) :
    ((splitEquiv Ω m n).symm f).2 i = f (Fin.natAdd m i) :=
  rfl

/-- Degree zero on the right: splitting off no coordinates recovers the original tuple. -/
theorem splitEquiv_zero_right (x : Fin m → Ω) (y : Fin 0 → Ω) (i : Fin m) :
    splitEquiv Ω m 0 (x, y) (Fin.castAdd 0 i) = x i :=
  Fin.append_left x y i

/-- Degree zero on the left: splitting off all coordinates recovers the original tuple. -/
theorem splitEquiv_zero_left (x : Fin 0 → Ω) (y : Fin n → Ω) (i : Fin n) :
    splitEquiv Ω 0 n (x, y) (Fin.natAdd 0 i) = y i :=
  Fin.append_right x y i

/-! ### Sections -/

namespace Graded

/-- **The section of a set of `(m + n)`-tuples at an `m`-tuple**: the `n`-tuples that
complete `x` to a member of `s`. Purely algebraic. -/
def sectionAt (s : Set (Fin (m + n) → Ω)) (x : Fin m → Ω) : Set (Fin n → Ω) :=
  {y | splitEquiv Ω m n (x, y) ∈ s}

@[simp]
theorem mem_sectionAt {s : Set (Fin (m + n) → Ω)} {x : Fin m → Ω} {y : Fin n → Ω} :
    y ∈ sectionAt s x ↔ splitEquiv Ω m n (x, y) ∈ s :=
  Iff.rfl

/-- The section of a preimage under the split is the fiber of the pair set. -/
theorem sectionAt_preimage_splitEquiv_symm (t : Set ((Fin m → Ω) × (Fin n → Ω)))
    (x : Fin m → Ω) :
    sectionAt ((splitEquiv Ω m n).symm ⁻¹' t) x = {y | (x, y) ∈ t} := by
  ext y
  simp

end Graded

/-! ### API tests -/

section Tests

/-- Both round-trips by bare `simp`. -/
example (p : (Fin m → Ω) × (Fin n → Ω)) (f : Fin (m + n) → Ω) :
    (splitEquiv Ω m n).symm (splitEquiv Ω m n p) = p
      ∧ splitEquiv Ω m n ((splitEquiv Ω m n).symm f) = f := by
  simp

/-- The coordinate rules, forward and inverse, by `simp`. -/
example (x : Fin m → Ω) (y : Fin n → Ω) (i : Fin m) (j : Fin n) (f : Fin (m + n) → Ω) :
    splitEquiv Ω m n (x, y) (Fin.castAdd n i) = x i
      ∧ splitEquiv Ω m n (x, y) (Fin.natAdd m j) = y j
      ∧ ((splitEquiv Ω m n).symm f).1 i = f (Fin.castAdd n i)
      ∧ ((splitEquiv Ω m n).symm f).2 j = f (Fin.natAdd m j) := by
  simp

/-- **An asymmetric `1 + 2` split**: the coordinates land where the orientation says. -/
example (x : Fin 1 → Ω) (y : Fin 2 → Ω) :
    splitEquiv Ω 1 2 (x, y) 0 = x 0 ∧ splitEquiv Ω 1 2 (x, y) 1 = y 0
      ∧ splitEquiv Ω 1 2 (x, y) 2 = y 1 := by
  exact ⟨splitEquiv_apply_castAdd x y 0, splitEquiv_apply_natAdd x y 0,
    splitEquiv_apply_natAdd x y 1⟩

/-- Membership in a section, by `simp`. -/
example (s : Set (Fin (1 + 2) → Ω)) (x : Fin 1 → Ω) (y : Fin 2 → Ω) :
    y ∈ Graded.sectionAt s x ↔ splitEquiv Ω 1 2 (x, y) ∈ s := by
  simp

/-- Both zero-degree boundaries. -/
example (x : Fin m → Ω) (y : Fin 0 → Ω) (i : Fin m) (x' : Fin 0 → Ω) (y' : Fin n → Ω)
    (j : Fin n) :
    splitEquiv Ω m 0 (x, y) (Fin.castAdd 0 i) = x i
      ∧ splitEquiv Ω 0 n (x', y') (Fin.natAdd 0 j) = y' j :=
  ⟨splitEquiv_zero_right x y i, splitEquiv_zero_left x' y' j⟩

end Tests

end Loeb
