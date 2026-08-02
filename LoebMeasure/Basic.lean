/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Ultraproduct.Permutation
import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# The `Loeb` project-facing surface

The generic ultraproduct API developed in `LoebMeasure/Ultraproduct/` lives in the
`Filter.Product` namespace, because it is about mathlib's dependent filter product and
nothing else — that is what makes it upstreamable. This module supplies the
project-facing names promised by `ARCHITECTURE.md` and the blueprint, so that

```lean
import LoebMeasure
open Loeb
```

gives a usable surface.

The alias is intentionally thin: `Loeb.Ultraproduct` fixes the filter to be an
*ultrafilter*, which is the setting the project's mathematics happens in, while the
underlying API stays generic in an arbitrary filter (ADR-0001). Everything proved for
`Filter.Product` therefore applies to `Loeb.Ultraproduct` without restatement, since
the alias is reducible.
-/

namespace Loeb

variable {ι : Type*}

/-- The ultraproduct of a family of types along an ultrafilter: mathlib's dependent
filter product, specialized to an ultrafilter.

This is an `abbrev`, so the whole `Filter.Product` API — representatives
(`Filter.Product.ofFun`), eliminators, `Filter.Product.map`, the product and
finite-power equivalences, reindexing, and the permutation action — applies directly
without restatement. -/
abbrev Ultraproduct (U : Ultrafilter ι) (X : ι → Type*) : Type _ :=
  (U : Filter ι).Product X

/-- The ultraproduct of a *constant* family, i.e. the ultrapower. -/
abbrev Ultrapower (U : Ultrafilter ι) (X : Type*) : Type _ :=
  Ultraproduct U fun _ ↦ X

section Examples

variable {U : Ultrafilter ι} {X : ι → Type*}

/-- The project-facing surface is usable: an element of an ultraproduct is represented
by a dependent function, and equality of representatives is eventual equality. -/
example (f g : (i : ι) → X i) (h : ∀ᶠ i in (U : Filter ι), f i = g i) :
    (Filter.Product.ofFun f : Ultraproduct U X) = Filter.Product.ofFun g := by
  simp [h]

/-- The generic API applies to the alias with no restatement: here a coordinatewise map
and a finite-power evaluation. -/
example {Y : ι → Type*} (φ : (i : ι) → X i → Y i) (f : (i : ι) → X i) :
    Filter.Product.map φ (Filter.Product.ofFun f : Ultraproduct U X)
      = Filter.Product.ofFun fun i ↦ φ i (f i) := by
  simp

example (k : ℕ) (f : (i : ι) → Fin k → X i) (j : Fin k) :
    Filter.Product.finPowerEquiv (l := (U : Filter ι)) (X := X) k
        (Filter.Product.ofFun f) j
      = Filter.Product.ofFun fun i ↦ f i j := by
  simp

end Examples

end Loeb
