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

Run in CI by `lake env lean scripts/AxiomAudit.lean`. Three jobs:

1. **Whole-library axiom hygiene.** `audit_project_declarations` enumerates *every*
   public declaration originating in a `LoebMeasure` module — by module provenance, not
   by a hand-kept list — and checks each depends only on the accepted axioms `propext`,
   `Classical.choice`, and `Quot.sound`. The check is transitive: `Lean.collectAxioms`
   walks the whole dependency closure.

2. **Documented API surface.** The named `assert_standard_axioms` roots below.

3. **Root-surface smoke test.** This file imports `LoebMeasure` and uses `Ultraproduct`
   *unqualified* after `open Loeb`, which is exactly the entry point the README
   documents. A regression in the facade breaks CI here rather than being discovered by
   a reader. Doing it in this file avoids a separate test library, and is only possible
   because the audit runs outside the `LoebMeasure` target — library modules must not
   import the root (see `CONTRIBUTING.md`).

## What changed, and why (#36)

The named roots used to *be* the coverage mechanism, with a reviewer checklist item
obliging contributors to extend them. That rule was missed twice in three opportunities
(#33, #35): new public proofs sat outside every audited closure and only human review
caught it. A measured failure rate, not a hypothetical one.

The fix removes the selection step rather than policing it. Coverage is now job 1, which
has no list to keep and so cannot be forgotten. A weaker design — "at least one audited
declaration per module" — was rejected during #33's review for a concrete reason: on both
misses the affected modules were *already* represented, so it would have passed while the
new declarations went unaudited, manufacturing confidence.

**The named roots remain, with a different job.** They document and smoke-test the
intended public API surface: a reader can see what the library claims to offer, and a
rename or removal breaks CI here. That is a communication artifact. It is no longer a
correctness dependency, so forgetting to extend it can no longer cause an audit gap.

## What is excluded, and why that is safe

Private declarations (`Lean.isPrivateName`) and compiler-internal details
(`Name.isInternalDetail` — equation lemmas, match auxiliaries, projections) are skipped,
or the report would be noise. This loses nothing: a private declaration used by a public
one is inside that public one's dependency closure, so its axioms are still caught.
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

/-- Every public declaration originating in a `LoebMeasure` module.

Provenance is by *module*, via the imported module data, so a declaration counts as the
project's exactly when a project module declares it — which is the population the old
checklist rule was trying to describe. Declarations this library states in mathlib
namespaces (`Filter.Product.ofFun` and the like) are therefore included, correctly:
they are ours, wherever their name lives. -/
def projectDeclarations (env : Environment) : Array Name := Id.run do
  let mut result := #[]
  for (moduleName, idx) in env.header.moduleNames.zipIdx do
    unless moduleName == `LoebMeasure || (`LoebMeasure).isPrefixOf moduleName do
      continue
    match env.header.moduleData[idx]? with
    | some data =>
      for n in data.constNames do
        unless Lean.isPrivateName n || n.isInternalDetail do
          result := result.push n
    | none => pure ()
  return result

/-- **The coverage check.** Audits every public declaration of every project module.

Unlike the named roots this needs no maintenance: adding a module or a public
declaration extends what is checked automatically. -/
elab "audit_project_declarations" : command => do
  let env ← getEnv
  let names := projectDeclarations env
  let mut offenders := #[]
  for name in names do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun a => !(acceptedAxioms.contains a)
    unless unexpected.isEmpty do
      offenders := offenders.push m!"{name}: {unexpected.toList}"
  unless offenders.isEmpty do
    throwError "public project declarations depending on non-standard axioms:\n\
      {MessageData.joinSep offenders.toList "\n"}\n\
      accepted: {acceptedAxioms}"
  logInfo m!"axiom audit: {names.size} public project declarations checked"

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

open Loeb in
/-- The wider generic API applies through the alias with no restatement: a
coordinatewise map and a finite-power evaluation. These live here rather than in
`LoebMeasure/Basic.lean`, which imports only what its aliases need. -/
example {ι : Type} {U : Ultrafilter ι} {X Y : ι → Type} (φ : (i : ι) → X i → Y i)
    (f : (i : ι) → X i) :
    Filter.Product.map φ (Filter.Product.ofFun f : Ultraproduct U X)
      = Filter.Product.ofFun fun i ↦ φ i (f i) := by
  simp

open Loeb in
example {ι : Type} {U : Ultrafilter ι} {X : ι → Type} (k : ℕ)
    (f : (i : ι) → Fin k → X i) (j : Fin k) :
    Filter.Product.finPowerEquiv (l := (U : Filter ι)) (X := X) k
        (Filter.Product.ofFun f) j
      = Filter.Product.ofFun fun i ↦ f i j := by
  simp

/-! ## Whole-library coverage

Job 1: every public declaration of every project module. No list to maintain. -/

audit_project_declarations

/-! ## Documented API surface

Job 2: the named entry points the library offers, which a reader can scan and which CI
breaks on if one is renamed or removed. Coverage no longer depends on this list being
complete — that is `audit_project_declarations`' job above. -/

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
assert_standard_axioms Filter.Product.map₂_map
assert_standard_axioms Filter.Product.finitePiEquiv
assert_standard_axioms Filter.Product.finPowerEquiv
assert_standard_axioms Filter.Product.map_finitePiEquiv_symm
assert_standard_axioms Filter.Product.finPowerEquiv_symm_ofFun
assert_standard_axioms Filter.Product.map_finPowerEquiv_symm

-- Internal sets
assert_standard_axioms Loeb.InternalSet
assert_standard_axioms Loeb.InternalSet.carrier
assert_standard_axioms Loeb.InternalSet.mem_carrier_ofFun
assert_standard_axioms Loeb.InternalSet.carrier_ofFun_nonempty_iff
assert_standard_axioms Loeb.InternalSet.carrier_injective
assert_standard_axioms Loeb.InternalSet.carrier_ofFun_singleton
assert_standard_axioms Loeb.InternalSet.singleton
assert_standard_axioms Loeb.InternalSet.carrier_singleton
assert_standard_axioms Loeb.InternalSet.instBooleanAlgebra
assert_standard_axioms Loeb.InternalSet.le_ofFun_iff
assert_standard_axioms Loeb.InternalSet.carrier_bot
assert_standard_axioms Loeb.InternalSet.carrier_top
assert_standard_axioms Loeb.InternalSet.carrier_inf
assert_standard_axioms Loeb.InternalSet.carrier_symmDiff
assert_standard_axioms Loeb.InternalSet.carrier_sup
assert_standard_axioms Loeb.InternalSet.carrier_compl
assert_standard_axioms Loeb.InternalSet.carrier_sdiff
assert_standard_axioms Loeb.InternalSet.carrier_mono
assert_standard_axioms Loeb.InternalSet.carriers
assert_standard_axioms Loeb.InternalSet.isSetAlgebra_carriers
assert_standard_axioms Loeb.InternalSet.isSetRing_carriers

-- Completeness criterion (mirror directory)
assert_standard_axioms MeasureTheory.OuterMeasure.isCaratheodory_of_measure_zero
assert_standard_axioms MeasureTheory.Measure.isComplete_of_caratheodory_le
assert_standard_axioms MeasureTheory.AddContent.measureCaratheodory_isComplete

-- Compact ultralimits (mirror directory)
assert_standard_axioms Ultrafilter.ultralimit
assert_standard_axioms Ultrafilter.tendsto_ultralimit
assert_standard_axioms Ultrafilter.tendsto_ultralimit_of_eventually_mem_compact
assert_standard_axioms Ultrafilter.ultralimit_congr
assert_standard_axioms Ultrafilter.ultralimit_const
assert_standard_axioms Ultrafilter.ultralimit_comp
assert_standard_axioms Ultrafilter.ultralimit_mono
assert_standard_axioms Ultrafilter.ultralimit_mono'
assert_standard_axioms Ultrafilter.ultralimit_le
assert_standard_axioms Ultrafilter.le_ultralimit
assert_standard_axioms Ultrafilter.ultralimit_eq_limUnder

-- Bounded real ultralimits
assert_standard_axioms Ultrafilter.tendsto_ultralimit_of_eventually_norm_le
assert_standard_axioms Ultrafilter.norm_ultralimit_le
assert_standard_axioms Ultrafilter.abs_ultralimit_le

-- Probability ultralimits
assert_standard_axioms Loeb.ultralimit_zero
assert_standard_axioms Loeb.ultralimit_one
assert_standard_axioms Loeb.ultralimit_add
assert_standard_axioms Loeb.ultralimit_const_mul
assert_standard_axioms Loeb.ultralimit_inv_natCast_eq_zero
assert_standard_axioms Loeb.ultralimit_le_of_le
assert_standard_axioms Loeb.ultralimit_le_one
assert_standard_axioms Loeb.ultralimit_le_one'
assert_standard_axioms Loeb.ultralimit_ne_top_of_le
assert_standard_axioms Loeb.ultralimit_ne_top

-- Internal content
assert_standard_axioms Loeb.internalContent
assert_standard_axioms Loeb.internalContent_ofFun
assert_standard_axioms Loeb.internalContent_bot
assert_standard_axioms Loeb.internalContent_top
assert_standard_axioms Loeb.internalContent_le_one
assert_standard_axioms Loeb.internalContent_ne_top
assert_standard_axioms Loeb.internalContent_mono
assert_standard_axioms Loeb.internalContent_sup_le
assert_standard_axioms Loeb.internalContent_sup_of_disjoint

-- The internal envelope
assert_standard_axioms Loeb.exists_internal_envelope
assert_standard_axioms Loeb.exists_internal_envelope_of_monotone

-- The content packaged as an AddContent
assert_standard_axioms Loeb.internalAddContent
assert_standard_axioms Loeb.internalAddContent_carrier

-- Sigma-subadditivity
assert_standard_axioms Loeb.internalAddContent_ne_top
assert_standard_axioms Loeb.internalAddContent_tendsto_zero
assert_standard_axioms Loeb.internalAddContent_iUnion_eq_tsum
assert_standard_axioms Loeb.internalAddContent_isSigmaSubadditive

-- The Loeb measure
assert_standard_axioms Loeb.loebMeasurableSpace
assert_standard_axioms Loeb.loebMeasure
assert_standard_axioms Loeb.loebMeasure_internal
assert_standard_axioms Loeb.measurableSet_internal
assert_standard_axioms Loeb.isProbabilityMeasure_loebMeasure
assert_standard_axioms Loeb.isComplete_loebMeasure
assert_standard_axioms Loeb.loebOuterMeasure
assert_standard_axioms Loeb.loebMeasure_eq_loebOuterMeasure

-- Internal outer approximation
assert_standard_axioms Loeb.loebMeasure_eq_iInf_internal
assert_standard_axioms Loeb.exists_internal_superset_content_lt

-- Measurable approximation and the internal-mod-null characterization
assert_standard_axioms Loeb.loebMeasure_eq_zero_iff
assert_standard_axioms Loeb.exists_internal_symmDiff_lt
assert_standard_axioms Loeb.exists_internal_subset_lt_content_add
assert_standard_axioms Loeb.exists_internal_symmDiff_eq_zero
assert_standard_axioms Loeb.loebMeasurable_iff_internal_mod_null

-- The measure of a point
assert_standard_axioms Loeb.internalContent_singleton
assert_standard_axioms Loeb.loebMeasure_singleton
assert_standard_axioms Loeb.nullSingletonClass_loebMeasure
assert_standard_axioms Loeb.loebMeasure_singleton_eq_one_of_subsingleton

-- Atomlessness
assert_standard_axioms Loeb.exists_internal_le_content_eq_half
assert_standard_axioms Loeb.exists_measurableSet_subset_measure_eq_half
assert_standard_axioms Loeb.exists_measurableSet_subset_measure_lt

-- Internal graphs
assert_standard_axioms Loeb.internalEdgeRelation
assert_standard_axioms Loeb.mem_carrier_internalEdgeRelation_ofFun
assert_standard_axioms Loeb.ultraproductGraph
assert_standard_axioms Loeb.ultraproductGraph_adj_ofFun
assert_standard_axioms Loeb.ultraproductGraph_adj_iff_mem
assert_standard_axioms Loeb.internalHomEvent
assert_standard_axioms Loeb.internalHomEvent_eq_ofFun
assert_standard_axioms Loeb.mem_carrier_internalHomEvent_ofFun
assert_standard_axioms Loeb.homomorphismSet
assert_standard_axioms Loeb.mem_tupleCarrier_internalHomEvent

-- The homomorphism density identity
assert_standard_axioms Loeb.finiteHomDensity
assert_standard_axioms Loeb.finiteHomDensity_bot
assert_standard_axioms Loeb.finiteHomDensity_fin_zero
assert_standard_axioms Loeb.finiteHomDensity_le_one
assert_standard_axioms Loeb.normalizedCounting_homomorphismSet
assert_standard_axioms Loeb.loebMeasure_internalHomEvent
assert_standard_axioms Loeb.loebMeasure_internalHomEvent_of_nonempty

-- Normalized counting measure
assert_standard_axioms Loeb.normalizedCounting
assert_standard_axioms Loeb.normalizedCounting_apply
assert_standard_axioms Loeb.normalizedCounting_apply_natCard
assert_standard_axioms Loeb.normalizedCounting_singleton
assert_standard_axioms Loeb.normalizedCounting_univ
assert_standard_axioms Loeb.normalizedCounting_le_one
assert_standard_axioms Loeb.normalizedCounting_apply_eq_sum
assert_standard_axioms Loeb.normalizedCounting_eq_uniformOn
assert_standard_axioms Loeb.instIsProbabilityMeasureNormalizedCounting

-- Diagonal selection
assert_standard_axioms Filter.IsCountablyIncomplete
assert_standard_axioms Filter.IsCountablyIncomplete.exists_antitone
assert_standard_axioms Filter.isCountablyIncomplete_of_le_cofinite
assert_standard_axioms Filter.hyperfilter_isCountablyIncomplete
assert_standard_axioms Filter.IsCountablyIncomplete.exists_forall_eventually_mem
assert_standard_axioms Filter.IsCountablyIncomplete.exists_forall_eventually_mem_of_antitone

-- Internal saturation
assert_standard_axioms Loeb.InternalSet.nonempty_iInter_carrier_of_antitone
assert_standard_axioms Loeb.InternalSet.nonempty_iInter_carrier_of_ne_bot
assert_standard_axioms Loeb.InternalSet.eventually_eq_bot_of_antitone_iInter_carrier_eq_empty

-- Internal maps and relations
assert_standard_axioms Loeb.InternalMap.toFun
assert_standard_axioms Loeb.InternalMap.toFun_comp
assert_standard_axioms Loeb.InternalMap.comp_ofFun
assert_standard_axioms Loeb.InternalSet.preimage
assert_standard_axioms Loeb.InternalSet.carrier_preimage
assert_standard_axioms Loeb.InternalSet.preimage_comp
assert_standard_axioms Loeb.InternalRelation.tupleCarrier
assert_standard_axioms Loeb.InternalRelation.carrier_comap
assert_standard_axioms Loeb.InternalRelation.tupleCarrier_comap
assert_standard_axioms Loeb.InternalRelation.tupleCarrier_top
assert_standard_axioms Loeb.InternalRelation.tupleCarrier_inf

-- Coordinate layer
assert_standard_axioms Filter.Product.eval
assert_standard_axioms Filter.Product.eval_finitePiEquiv_symm
assert_standard_axioms Filter.Product.reindex
assert_standard_axioms Filter.Product.permute
assert_standard_axioms Filter.Product.finitePiEquiv_reindex
assert_standard_axioms Filter.Product.finPowerEquiv_permute
-- These two transitively cover their generic forms and `reindex_piMk`.
assert_standard_axioms Filter.Product.reindex_finPowerEquiv_symm
assert_standard_axioms Filter.Product.permute_finPowerEquiv_symm
assert_standard_axioms Filter.Product.reindex_map
assert_standard_axioms Filter.Product.permute_map
