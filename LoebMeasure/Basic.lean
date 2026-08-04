/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Ultraproduct.Basic
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

This module imports only what the aliases themselves need, per the layering rule in
`ARCHITECTURE.md`; `LoebMeasure.lean` is the umbrella that exposes the full API.
Examples exercising the wider API against the alias live in `scripts/AxiomAudit.lean`,
which already imports the root.
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

end Examples

end Loeb
