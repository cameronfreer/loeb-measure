/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Axiom audit

Run in CI by `lake env lean scripts/AxiomAudit.lean`. Two jobs:

1. **Axiom hygiene.** Every declaration named below is checked to depend only on the
   accepted axioms `propext`, `Classical.choice`, and `Quot.sound`. The check is
   transitive: `Lean.collectAxioms` walks the whole dependency closure, so an axiom
   introduced anywhere beneath a listed declaration fails the build.

2. **Root-surface smoke test.** This file imports `LoebMeasure` and uses `Ultraproduct`
   *unqualified* after `open Loeb`, which is exactly the entry point the README
   documents. A regression in the facade breaks CI here rather than being discovered by
   a reader. Doing it in this file avoids a separate test library, and is only possible
   because the audit runs outside the `LoebMeasure` target — library modules must not
   import the root (see `CONTRIBUTING.md`).

## Scope

This audits the **named public boundary declarations** listed below: selected public
entry points from each module, chosen so that the transitive closure covers the
substance of the library. It is deliberately *not* a whole-library enumeration, and the
README says so.

Changing a public module or capability obliges you to revisit this list — keeping it
representative is a semantic judgement that no automated check can make, so it is a
reviewer checklist item in `CONTRIBUTING.md` and the pull-request template.
-/

open Lean Elab Command

namespace LoebMeasure.AxiomAudit

/-- The axioms this project accepts. Anything else is a build failure. -/
def acceptedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Fails unless the given declaration depends only on `acceptedAxioms`, transitively. -/
elab "assert_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let unexpected := axioms.filter fun a => !(acceptedAxioms.contains a)
  unless unexpected.isEmpty do
    throwError "{name} depends on non-standard axioms: {unexpected.toList}\n\
      accepted: {acceptedAxioms}"

end LoebMeasure.AxiomAudit

/-! ## Root-surface smoke test

The literal documented path: `import LoebMeasure`, `open Loeb`, then `Ultraproduct`
with no namespace prefix. -/

open Loeb in
/-- The facade is reachable unqualified, and the generic API applies through it. -/
example {ι : Type} (U : Ultrafilter ι) (X : ι → Type) (f : (i : ι) → X i) :
    Ultraproduct U X :=
  Filter.Product.ofFun f

open Loeb in
example {ι : Type} (U : Ultrafilter ι) (X : Type) (f : ι → X) : Ultrapower U X :=
  Filter.Product.ofFun f

/-! ## Audited boundary declarations -/

-- Project facade
assert_standard_axioms Loeb.Ultraproduct
assert_standard_axioms Loeb.Ultrapower

-- Representative layer
assert_standard_axioms Filter.Product.ofFun
assert_standard_axioms Filter.Product.ofFun_eq_ofFun
assert_standard_axioms Filter.Product.inductionOn
assert_standard_axioms Filter.Product.liftOn

-- Functor layer
assert_standard_axioms Filter.Product.map
assert_standard_axioms Filter.Product.map_comp
assert_standard_axioms Filter.Product.map_congr

-- Finite-product layer
assert_standard_axioms Filter.Product.prodEquiv
assert_standard_axioms Filter.Product.map_prodEquiv_symm
assert_standard_axioms Filter.Product.map_fst_prodEquiv_symm
assert_standard_axioms Filter.Product.map_snd_prodEquiv_symm
assert_standard_axioms Filter.Product.map₂
assert_standard_axioms Filter.Product.map_map₂
assert_standard_axioms Filter.Product.finitePiEquiv
assert_standard_axioms Filter.Product.finPowerEquiv
assert_standard_axioms Filter.Product.map_finitePiEquiv_symm
assert_standard_axioms Filter.Product.finPowerEquiv_symm_ofFun
assert_standard_axioms Filter.Product.map_finPowerEquiv_symm

-- Coordinate layer
assert_standard_axioms Filter.Product.eval
assert_standard_axioms Filter.Product.eval_finitePiEquiv_symm
assert_standard_axioms Filter.Product.reindex
assert_standard_axioms Filter.Product.permute
assert_standard_axioms Filter.Product.finitePiEquiv_reindex
assert_standard_axioms Filter.Product.finPowerEquiv_permute
-- These two transitively cover their generic forms and `reindex_finitePiMk`.
assert_standard_axioms Filter.Product.reindex_finPowerEquiv_symm
assert_standard_axioms Filter.Product.permute_finPowerEquiv_symm
assert_standard_axioms Filter.Product.reindex_map
assert_standard_axioms Filter.Product.permute_map
