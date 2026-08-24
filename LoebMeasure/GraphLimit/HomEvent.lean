/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.GraphLimit.InternalGraph

/-!
# The internal homomorphism event

For a fixed pattern `F : SimpleGraph (Fin k)` and stage graphs `G : ∀ i, SimpleGraph (X i)`,
the internal set of `k`-tuples that preserve edges.

## One definition, one alternative description

`internalHomEvent` is built **only** as a finite intersection of coordinate pullbacks of
`internalEdgeRelation`, which is what `InternalRelation.comap` exists for and what
exercises the coordinate layer. The direct stagewise description appears as a theorem,
`carrier_internalHomEvent_ofFun`, not as a competing definition — so there is one object
and two ways of computing with it.

## Indexing by ordered pairs

The intersection runs over the **ordered** adjacent pairs in `Fin k × Fin k`, not over
`F.edgeFinset : Finset (Sym2 (Fin k))`. Sym2 would force a choice of orientation to build
the coordinate map, and no choice is canonical; indexing by ordered pairs makes `![u, v]`
canonical instead. Each undirected edge is therefore intersected twice, once per
orientation, which is harmless: the two pullbacks realize the same condition because both
`F` and each `G i` are symmetric.

## Where finiteness is used, and where it is not

Exactly once, in `carrier_internalHomEvent_ofFun`, to move a universal quantifier through
`∀ᶠ` via `Filter.eventually_all_finset`. Stagewise, each edge separately gives an eventual
condition; turning "for every edge, eventually" into "eventually, for every edge" is a
finite-intersection step and nothing else. `Fin k × Fin k` being a `Fintype` is what makes
it available.

The **realized** rule needs no such move. `tupleCarrier` is a preimage, so it takes the
finite intersection to a finite intersection of sets outright, and the quantifier never
has to cross a filter.

## Hypotheses

No additional stage hypotheses: no finiteness, no nonemptiness, no measurability, no
countable incompleteness, and no measure-layer import. Counting and the Loeb measure enter
at G3.

The event itself and its representative computation are pure internal-relation
constructions and use no ultrafilter property at all. **Properness** enters only through
`ultraproductGraph`, which G1 already built with it, and so appears only in the realized
rule by way of that graph's looplessness.

## Scope

The event and its two computation rules. The density identity, any counting or
normalization, and the packaging of a tuple as a `SimpleGraph.Hom` are all later — the raw
adjacency-preservation predicate is more useful here, and bundling can wait until G3's
counting interface actually asks for it.
-/

namespace Loeb

open Filter

variable {ι : Type*} {U : Ultrafilter ι} {X : ι → Type*} {k : ℕ}

/-- The ordered adjacent pairs of the pattern graph, the index set of the intersection.

`private`: it is an implementation detail of the definition, and the public rules quantify
over `F.Adj u v` directly rather than over membership here. -/
private noncomputable def adjPairs (F : SimpleGraph (Fin k)) : Finset (Fin k × Fin k) :=
  letI := Classical.decRel F.Adj
  Finset.univ.filter fun e ↦ F.Adj e.1 e.2

private theorem mem_adjPairs {F : SimpleGraph (Fin k)} {e : Fin k × Fin k} :
    e ∈ adjPairs F ↔ F.Adj e.1 e.2 := by
  classical
  rw [adjPairs]
  simp

/-- **The internal homomorphism event**: the internal set of stagewise `k`-tuples that
preserve every edge of `F`.

Built as a finite intersection of coordinate pullbacks — one per *ordered* adjacent pair —
of the internal edge relation. This is the construction `InternalRelation.comap` was built
for; `carrier_internalHomEvent_ofFun` gives the equivalent direct stagewise description. -/
noncomputable def internalHomEvent (U : Ultrafilter ι) (F : SimpleGraph (Fin k))
    (G : ∀ i, SimpleGraph (X i)) : InternalRelation U X k :=
  (adjPairs F).inf fun e ↦
    InternalRelation.comap ![e.1, e.2] (internalEdgeRelation U G)

/-- Carriers take a finite infimum to a finite intersection.

`private`, and stated by `Finset` induction over `InternalSet.carrier_top` and
`InternalSet.carrier_inf`. It is generic, but has a single consumer, so it stays here
rather than enlarging the Boolean API speculatively. -/
private theorem carrier_finset_inf {Y : ι → Type*} {κ : Type*} (E : Finset κ)
    (f : κ → InternalSet U Y) :
    InternalSet.carrier (E.inf f) = ⋂ e ∈ E, InternalSet.carrier (f e) := by
  classical
  induction E using Finset.induction_on with
  | empty => rw [Finset.inf_empty, InternalSet.carrier_top]; simp
  | insert a E ha ih => rw [Finset.inf_insert, InternalSet.carrier_inf, ih]; simp

/-- The same for realized tuples, through `tupleCarrier_top` and `tupleCarrier_inf`. -/
private theorem tupleCarrier_finset_inf {κ : Type*} (E : Finset κ)
    (f : κ → InternalRelation U X k) :
    InternalRelation.tupleCarrier (E.inf f)
      = ⋂ e ∈ E, InternalRelation.tupleCarrier (f e) := by
  classical
  induction E using Finset.induction_on with
  | empty => rw [Finset.inf_empty, InternalRelation.tupleCarrier_top]; simp
  | insert a E ha ih =>
    rw [Finset.inf_insert, InternalRelation.tupleCarrier_inf, ih]; simp

/-- Pulling the edge relation back along `![u, v]` reads off coordinates `u` and `v`. -/
private theorem mem_carrier_comap_pair (G : ∀ i, SimpleGraph (X i)) (u v : Fin k)
    (p : (i : ι) → Fin k → X i) :
    (Filter.Product.ofFun p : Ultraproduct U fun i ↦ Fin k → X i)
        ∈ InternalSet.carrier
          (InternalRelation.comap ![u, v] (internalEdgeRelation U G)) ↔
      ∀ᶠ i in (U : Filter ι), (G i).Adj (p i u) (p i v) := by
  rw [InternalRelation.carrier_comap, Set.mem_preimage,
    Filter.Product.reindex_ofFun, mem_carrier_internalEdgeRelation_ofFun]
  rfl

/-- **The representative computation rule.**

A represented tuple family lies in the event exactly when it eventually preserves every
edge stagewise. This is the only place finiteness of the pattern is used: it is what lets
`Filter.eventually_all_finset` move the edge quantifier through `∀ᶠ`. -/
@[simp]
theorem carrier_internalHomEvent_ofFun (F : SimpleGraph (Fin k))
    (G : ∀ i, SimpleGraph (X i)) (p : (i : ι) → Fin k → X i) :
    (Filter.Product.ofFun p : Ultraproduct U fun i ↦ Fin k → X i)
        ∈ InternalSet.carrier (internalHomEvent U F G) ↔
      ∀ᶠ i in (U : Filter ι), ∀ ⦃u v⦄, F.Adj u v → (G i).Adj (p i u) (p i v) := by
  rw [internalHomEvent, carrier_finset_inf]
  simp only [Set.mem_iInter, mem_carrier_comap_pair]
  -- Finiteness enters here, and only here.
  rw [← Finset.eventually_all (I := adjPairs F)]
  exact eventually_congr (Eventually.of_forall fun _ ↦
    ⟨fun h _ _ huv ↦ h ⟨_, _⟩ (mem_adjPairs.2 huv), fun h _ he ↦ h (mem_adjPairs.1 he)⟩)

/-- **The realized computation rule.**

A tuple of ultraproduct points lies in the realized event exactly when it is a graph
homomorphism into `ultraproductGraph U G` — stated as raw adjacency preservation, which is
what G3's counting will use.

Unlike the representative rule this needs no finiteness: `tupleCarrier` is a preimage, so
the finite intersection becomes a finite intersection of sets and no quantifier crosses a
filter.

Deliberately **not** `@[simp]`: `InternalRelation.mem_tupleCarrier` already rewrites the
same head, and two simp lemmas on one pattern would make which fires depend on ordering.
Callers `rw` this one explicitly. -/
theorem mem_tupleCarrier_internalHomEvent (F : SimpleGraph (Fin k))
    (G : ∀ i, SimpleGraph (X i)) (x : Fin k → Ultraproduct U X) :
    x ∈ InternalRelation.tupleCarrier (internalHomEvent U F G) ↔
      ∀ ⦃u v⦄, F.Adj u v → (ultraproductGraph U G).Adj (x u) (x v) := by
  rw [internalHomEvent, tupleCarrier_finset_inf]
  simp only [Set.mem_iInter, InternalRelation.tupleCarrier_comap, Set.mem_preimage,
    mem_adjPairs]
  constructor
  · intro h u v huv
    have := h ⟨u, v⟩ huv
    rwa [ultraproductGraph_adj_iff_mem, show ![x u, x v] = x ∘ ![u, v] from ?_]
    funext a
    fin_cases a <;> rfl
  · rintro h ⟨u, v⟩ huv
    rw [show x ∘ ![u, v] = ![x u, x v] from ?_]
    · exact h huv
    funext a
    fin_cases a <;> rfl

/-! ### API tests -/

section Tests

/-- **The realized rule is homomorphism preservation**, in the shape G3 will consume. -/
example (F : SimpleGraph (Fin k)) (G : ∀ i, SimpleGraph (X i))
    (x : Fin k → Ultraproduct U X)
    (h : ∀ ⦃u v⦄, F.Adj u v → (ultraproductGraph U G).Adj (x u) (x v)) :
    x ∈ InternalRelation.tupleCarrier (internalHomEvent U F G) := by
  rw [mem_tupleCarrier_internalHomEvent]
  exact h

/-- **And it round-trips**: membership gives back edge preservation. -/
example (F : SimpleGraph (Fin k)) (G : ∀ i, SimpleGraph (X i))
    (x : Fin k → Ultraproduct U X)
    (h : x ∈ InternalRelation.tupleCarrier (internalHomEvent U F G)) {u v : Fin k}
    (huv : F.Adj u v) : (ultraproductGraph U G).Adj (x u) (x v) := by
  rw [mem_tupleCarrier_internalHomEvent] at h
  exact h huv

/-- **The representative rule**, with the eventual quantifier outermost. -/
example (F : SimpleGraph (Fin k)) (G : ∀ i, SimpleGraph (X i))
    (p : (i : ι) → Fin k → X i)
    (h : ∀ᶠ i in (U : Filter ι), ∀ ⦃u v⦄, F.Adj u v → (G i).Adj (p i u) (p i v)) :
    (Filter.Product.ofFun p : Ultraproduct U fun i ↦ Fin k → X i)
      ∈ InternalSet.carrier (internalHomEvent U F G) := by
  simpa using h

/-- **The empty pattern is the whole space.** With no edges the intersection is empty, so
the event is `⊤` — a check that the orientation of the construction is right, since an
empty intersection of *unions* would have given `⊥`. -/
example (G : ∀ i, SimpleGraph (X i)) (x : Fin k → Ultraproduct U X) :
    x ∈ InternalRelation.tupleCarrier (internalHomEvent U (⊥ : SimpleGraph (Fin k)) G) := by
  rw [mem_tupleCarrier_internalHomEvent]
  exact fun _ _ h ↦ h.elim

/-- **A single edge on two vertices** recovers the edge relation itself, up to the
realized form: a pair is in the event exactly when it is adjacent. -/
example (G : ∀ i, SimpleGraph (X i)) (x : Fin 2 → Ultraproduct U X) :
    x ∈ InternalRelation.tupleCarrier (internalHomEvent U (⊤ : SimpleGraph (Fin 2)) G) ↔
      ∀ ⦃u v⦄, u ≠ v → (ultraproductGraph U G).Adj (x u) (x v) := by
  rw [mem_tupleCarrier_internalHomEvent]
  simp only [SimpleGraph.top_adj]

/-- **A genuinely dependent family** of stage graphs on varying vertex types. -/
example (U : Ultrafilter ℕ) (F : SimpleGraph (Fin 3))
    (G : ∀ i : ℕ, SimpleGraph (Fin (i + 1))) (p : (i : ℕ) → Fin 3 → Fin (i + 1))
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ ⦃u v⦄, F.Adj u v → (G i).Adj (p i u) (p i v)) :
    (Filter.Product.ofFun p : Ultraproduct U fun i ↦ Fin 3 → Fin (i + 1))
      ∈ InternalSet.carrier (internalHomEvent U F G) := by
  simpa using h

/-- The event **is** an internal relation, so the coordinate API applies to it unchanged —
here pulled back along a further selection. That closure is what lets G3 treat it like any
other internal set and take its Loeb measure. -/
example (F : SimpleGraph (Fin k)) (G : ∀ i, SimpleGraph (X i)) (σ : Fin k → Fin 5)
    (x : Fin 5 → Ultraproduct U X) :
    x ∈ InternalRelation.tupleCarrier ((internalHomEvent U F G).comap σ) ↔
      x ∘ σ ∈ InternalRelation.tupleCarrier (internalHomEvent U F G) := by
  simp

end Tests

end Loeb
