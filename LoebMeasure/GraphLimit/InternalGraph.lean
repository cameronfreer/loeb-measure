/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Internal.Relation
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Internal edge relations and the ultraproduct graph

A family of stage graphs gives two different objects, and keeping them apart is the point
of this module:

* `internalEdgeRelation U G : InternalRelation U X 2` — stagewise adjacency, living on
  the **ultraproduct of pairs** `Ultraproduct U (fun i ↦ Fin 2 → X i)`. This is the side
  internality and the Loeb measure are defined on;
* `ultraproductGraph U G : SimpleGraph (Ultraproduct U X)` — a genuine simple graph on the
  ultraproduct, whose adjacency is membership of the corresponding **ordered pair** in the
  relation above.

The second is called the *ultraproduct graph* rather than the "internal graph" precisely
so that the realized graph is not confused with the internal relation it comes from. They
have different ambient types, and `Filter.Product.finPowerEquiv` is what transports between
them — appearing only at that boundary, never inside a definition.

## Ordering convention

`ultraproductGraph U G |>.Adj x y` is membership of `![x, y]`: **coordinate `0` is the
left endpoint and coordinate `1` is the right endpoint**. This is pinned by compiled tests
rather than by this sentence, since a silently reversed convention would still typecheck —
edge relations are symmetric, so nothing downstream would complain.

## Symmetry and irreflexivity are transported, not imposed

`SimpleGraph.fromRel r` is `a ≠ b ∧ (r a b ∨ r b a)`: it symmetrizes and de-loops
*whatever* relation it is given. Applied to the edge relation below it would in fact
produce the very same graph, since that relation is already symmetric and irreflexive — so
this is not a correctness question, and no test can distinguish the two.

What it changes is where the obligation lives. With `fromRel`, the structure would come
from the wrapper and nothing in this module would witness that the stage graphs'
symmetry and looplessness transport at all; the same wrapper would produce a well-formed
graph from a relation with neither property. Building the fields directly makes the
elaborator demand those transport proofs, so they are checked rather than assumed.

The transport needs only ordinary filter reasoning: `Filter.Eventually.mono` over the
stage proofs, plus properness for `loopless` — an eventually false statement is false.

## Hypotheses

No *additional* ones: no finiteness, no nonemptiness, no measurability, no countable
incompleteness, and nothing from the measure layer is imported. A graph structure on an
ultraproduct is combinatorics, and the Loeb measure enters only at G2 and beyond.

What `U : Ultrafilter ι` does supply, and what is genuinely used, is **properness** —
`Filter.NeBot` — for looplessness. The ultrafilter *dichotomy* is not used anywhere here.

## Scope

The two objects and the computation rule relating them. The internal homomorphism event is
G2, and is where `InternalRelation.comap` and finite intersections first enter. There is
deliberately **no bundled or quotient `InternalGraph` type**: the stage family together
with its internal edge relation is enough for M4, and bundling can wait for a second
consumer.
-/

namespace Loeb

open Filter

variable {ι : Type*} {U : Ultrafilter ι} {X : ι → Type*}

/-- **Stagewise adjacency as an internal relation.**

An element of `InternalRelation U X 2`, that is, an internal set on the stagewise pairs.
Note the side: this is *not* a relation on pairs of ultraproduct elements — see
`ultraproductGraph` for that, and `Internal/Relation.lean` for why the stagewise side is
the primary one. -/
def internalEdgeRelation (U : Ultrafilter ι) (G : ∀ i, SimpleGraph (X i)) :
    InternalRelation U X 2 :=
  Filter.Product.ofFun fun i ↦ {p : Fin 2 → X i | (G i).Adj (p 0) (p 1)}

/-- Membership in the internal edge relation is eventual stagewise adjacency. -/
@[simp]
theorem mem_carrier_internalEdgeRelation_ofFun (G : ∀ i, SimpleGraph (X i))
    (p : (i : ι) → Fin 2 → X i) :
    (Filter.Product.ofFun p : Ultraproduct U fun i ↦ Fin 2 → X i)
        ∈ InternalSet.carrier (internalEdgeRelation U G) ↔
      ∀ᶠ i in (U : Filter ι), (G i).Adj (p i 0) (p i 1) :=
  Iff.rfl

/-- The stagewise pair family behind a pair of represented points. Named because it is
what `finPowerEquiv` transports, and it appears in both directions of the computation
rule below. -/
private theorem finPowerEquiv_symm_pair (x y : (i : ι) → X i) :
    (Filter.Product.finPowerEquiv (l := (U : Filter ι)) (X := X) 2).symm
        ![(Filter.Product.ofFun x : Ultraproduct U X), Filter.Product.ofFun y]
      = Filter.Product.ofFun fun i ↦ ![x i, y i] := by
  refine Eq.trans (congrArg _ ?_)
    (Filter.Product.finPowerEquiv_symm_ofFun (l := (U : Filter ι)) (X := X) 2
      fun i ↦ ![x i, y i])
  funext a
  fin_cases a <;> rfl

/-- The realized adjacency relation, before it is packaged as a graph.

`private` and named only so that symmetry and irreflexivity can be discharged against the
computation rule below rather than against an anonymous field body. -/
private def edgeRel (U : Ultrafilter ι) (G : ∀ i, SimpleGraph (X i)) :
    Ultraproduct U X → Ultraproduct U X → Prop :=
  fun x y ↦ ![x, y] ∈ InternalRelation.tupleCarrier (internalEdgeRelation U G)

/-- The computation rule, at the level of the bare relation. Together with the private
bridge above, this is where `Filter.Product.finPowerEquiv` is discharged; no *definition*
in this module mentions it. -/
private theorem edgeRel_ofFun (G : ∀ i, SimpleGraph (X i)) (x y : (i : ι) → X i) :
    edgeRel U G (Filter.Product.ofFun x) (Filter.Product.ofFun y) ↔
      ∀ᶠ i in (U : Filter ι), (G i).Adj (x i) (y i) := by
  rw [edgeRel, InternalRelation.mem_tupleCarrier, finPowerEquiv_symm_pair,
    mem_carrier_internalEdgeRelation_ofFun]
  simp

/-- **The ultraproduct graph.**

Adjacency of `x` and `y` is membership of the ordered pair `![x, y]` in the realized edge
relation. Symmetry and irreflexivity are transported from the stage graphs rather than
imposed by `SimpleGraph.fromRel`, so this definition would fail to elaborate if the
transport did not work.

Irreflexivity is the direction that uses **properness** of the ultrafilter: an eventually
false statement is false, which is what turns stagewise looplessness into looplessness
here. -/
def ultraproductGraph (U : Ultrafilter ι) (G : ∀ i, SimpleGraph (X i)) :
    SimpleGraph (Ultraproduct U X) where
  Adj := edgeRel U G
  symm := ⟨by
    intro x y
    induction x, y using Filter.Product.inductionOn₂ with
    | _ x' y' =>
      rw [edgeRel_ofFun, edgeRel_ofFun]
      exact fun h ↦ h.mono fun _ hi ↦ hi.symm⟩
  loopless := ⟨by
    intro x
    induction x using Filter.Product.inductionOn with
    | _ x' =>
      rw [edgeRel_ofFun]
      exact fun h ↦ (h.mono fun i hi ↦ (G i).loopless.irrefl _ hi).exists.elim fun _ hi ↦ hi⟩

/-- **The computation rule.** Adjacency in the ultraproduct graph is eventual stagewise
adjacency.

This is the whole interface: everything downstream should go through it rather than
unfolding `ultraproductGraph`. -/
@[simp]
theorem ultraproductGraph_adj_ofFun (G : ∀ i, SimpleGraph (X i)) (x y : (i : ι) → X i) :
    (ultraproductGraph U G).Adj (Filter.Product.ofFun x) (Filter.Product.ofFun y) ↔
      ∀ᶠ i in (U : Filter ι), (G i).Adj (x i) (y i) :=
  edgeRel_ofFun G x y

/-- Adjacency in tuple form, for callers already holding a pair as a `Fin 2` tuple. Kept
separate from the definition so that `ultraproductGraph`'s field is not the public seam. -/
theorem ultraproductGraph_adj_iff_mem (G : ∀ i, SimpleGraph (X i))
    (x y : Ultraproduct U X) :
    (ultraproductGraph U G).Adj x y ↔
      ![x, y] ∈ InternalRelation.tupleCarrier (internalEdgeRelation U G) :=
  Iff.rfl

/-! ### API tests -/

section Tests

/-- **The computation rule fires by `simp`.** -/
example (G : ∀ i, SimpleGraph (X i)) (x y : (i : ι) → X i)
    (h : ∀ᶠ i in (U : Filter ι), (G i).Adj (x i) (y i)) :
    (ultraproductGraph U G).Adj (Filter.Product.ofFun x) (Filter.Product.ofFun y) := by
  simp [h]

/-- **Coordinate `0` is the left endpoint**: the tuple whose zeroth entry is `x` and whose
first entry is `y` witnesses `Adj x y`, in that order. Compiled so the convention cannot
drift. -/
example (G : ∀ i, SimpleGraph (X i)) (x y : Ultraproduct U X)
    (h : (ultraproductGraph U G).Adj x y) :
    ∃ p : Fin 2 → Ultraproduct U X, p 0 = x ∧ p 1 = y ∧
      p ∈ InternalRelation.tupleCarrier (internalEdgeRelation U G) :=
  ⟨![x, y], rfl, rfl, h⟩

/-- **And coordinate `1` is the right endpoint**, stated from the other side: a tuple in
the realized relation gives adjacency of its zeroth entry to its first, not the reverse.
Together with the previous test this pins the ordering. -/
example (G : ∀ i, SimpleGraph (X i)) (p : Fin 2 → Ultraproduct U X)
    (h : p ∈ InternalRelation.tupleCarrier (internalEdgeRelation U G)) :
    (ultraproductGraph U G).Adj (p 0) (p 1) := by
  rw [ultraproductGraph_adj_iff_mem]
  have : ![p 0, p 1] = p := by
    funext a; fin_cases a <;> rfl
  rwa [this]

/-- **Symmetry is genuinely transported**: it holds because the stage graphs are
symmetric, and is available on the realized graph. -/
example (G : ∀ i, SimpleGraph (X i)) (x y : Ultraproduct U X)
    (h : (ultraproductGraph U G).Adj x y) : (ultraproductGraph U G).Adj y x :=
  h.symm

/-- **Irreflexivity likewise.** On an ultrafilter this needs properness: an eventually
false statement is false. -/
example (G : ∀ i, SimpleGraph (X i)) (x : Ultraproduct U X) :
    ¬ (ultraproductGraph U G).Adj x x :=
  (ultraproductGraph U G).irrefl

/-- **A genuinely dependent family** of stage graphs, on varying vertex types. -/
example (U : Ultrafilter ℕ) (G : ∀ i : ℕ, SimpleGraph (Fin (i + 1)))
    (x y : (i : ℕ) → Fin (i + 1))
    (h : ∀ᶠ i in (U : Filter ℕ), (G i).Adj (x i) (y i)) :
    (ultraproductGraph U G).Adj (Filter.Product.ofFun x) (Filter.Product.ofFun y) := by
  simp [h]

/-- **Nonadjacency transfers**: eventually non-adjacent stages give a non-adjacent pair in
the ultraproduct graph.

The proof uses **properness**, not the ultrafilter dichotomy — an eventually false
statement cannot also be eventually true. Note this test does *not* detect a `fromRel`
wrapper: since the edge relation is already symmetric and irreflexive, wrapping it would
give the same graph and the test would still pass. -/
example (G : ∀ i, SimpleGraph (X i)) (x y : (i : ι) → X i)
    (h : ∀ᶠ i in (U : Filter ι), ¬ (G i).Adj (x i) (y i)) :
    ¬ (ultraproductGraph U G).Adj (Filter.Product.ofFun x) (Filter.Product.ofFun y) := by
  rw [ultraproductGraph_adj_ofFun]
  intro hadj
  obtain ⟨i, hne, hi⟩ := (h.and hadj).exists
  exact hne hi

/-- The internal edge relation is available on its own, on the stagewise side, with no
graph structure in sight — the separation the module docstring describes. -/
example (G : ∀ i, SimpleGraph (X i)) : InternalRelation U X 2 :=
  internalEdgeRelation U G

end Tests

end Loeb
