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

## One definition, one proved-equal description

`internalHomEvent` is built **only** as a finite intersection of coordinate pullbacks of
`internalEdgeRelation`, which is what `InternalRelation.comap` exists for and what
exercises the coordinate layer.

The direct stagewise description appears as `internalHomEvent_eq_ofFun`, an **equality of
internal sets** and not merely a carrier characterization. The distinction matters here:
without nonempty fibers `InternalSet.carrier` is not known to be injective, so two internal
sets with the same carrier need not be equal, and this module assumes no nonemptiness. So
there is one object with two descriptions, proved the same as elements of
`InternalRelation`.

## Indexing by ordered pairs

The intersection runs over the **ordered** adjacent pairs in `Fin k × Fin k`, not over
`F.edgeFinset : Finset (Sym2 (Fin k))`. Sym2 would force a choice of orientation to build
the coordinate map, and no choice is canonical; indexing by ordered pairs makes `![u, v]`
canonical instead. Each undirected edge is therefore intersected twice, once per
orientation, which is harmless: the two pullbacks realize the same condition because both
`F` and each `G i` are symmetric.

## Where finiteness is used

**Structurally, in one place.** Finiteness of the pattern is discharged where `adjPairs`
enumerates `Fin k × Fin k` with `Finset.univ`; from there on the object is a `Finset.inf`
and the two inductions below (`finset_inf_ofFun` and `tupleCarrier_finset_inf`) are
generic over an already-given `Finset`, using no finiteness of `Fin k` themselves.

What is worth noting is that **no filter-level finite-intersection argument is needed
anywhere**. `internalHomEvent_eq_ofFun` collapses the intersection at the level of
representative functions — the two sides are equal as functions, so even the quotient
congruence is `congrArg`, not an eventual-equality step — and the representative
membership rule is then just `InternalSet.mem_carrier_ofFun`. The edge quantifier is never
commuted through `∀ᶠ`. The realized rule likewise needs no such argument: `tupleCarrier`
is a preimage, so it takes the finite infimum to an intersection of sets outright.

## Hypotheses

No additional stage hypotheses: no finiteness, no nonemptiness, no measurability, no
countable incompleteness, and no measure-layer import. Counting and the Loeb measure enter
at G3.

Nothing here uses an ultrafilter property, **properness included**. The realized rule
mentions `ultraproductGraph`, whose *construction* in G1 needed properness for
looplessness, but no proof in this module consumes it: the realized rule goes through
`ultraproductGraph_adj_iff_mem`, which is `Iff.rfl`.

## Scope

The event and its two computation rules. The density identity, any counting or
normalization, and the packaging of a tuple as a `SimpleGraph.Hom` are all later — the raw
adjacency-preservation predicate is more useful here, and bundling can wait until G3's
counting interface actually asks for it.
-/

namespace Loeb

open Filter

variable {ι : Type*} {U : Ultrafilter ι} {X : ι → Type*} {k : ℕ}

/-- **The set of graph homomorphisms** `F → G`, as a plain set of vertex maps.

Every edge-preserving map, neither induced nor injective — the count E4 fixed. Kept as a
bare `Set (V → W)` rather than as `SimpleGraph.Hom`, since both consumers want a set: this
module to describe `internalHomEvent`, and G3 to count it. -/
def homomorphismSet {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : Set (V → W) :=
  {f | ∀ ⦃u v⦄, F.Adj u v → G.Adj (f u) (f v)}

@[simp]
theorem mem_homomorphismSet {V W : Type*} {F : SimpleGraph V} {G : SimpleGraph W}
    {f : V → W} :
    f ∈ homomorphismSet F G ↔ ∀ ⦃u v⦄, F.Adj u v → G.Adj (f u) (f v) :=
  Iff.rfl

/-- With no edges to preserve, every map is a homomorphism. -/
@[simp]
theorem homomorphismSet_bot {V W : Type*} (G : SimpleGraph W) :
    homomorphismSet (⊥ : SimpleGraph V) G = Set.univ := by
  ext f
  simp [homomorphismSet]

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
for; `internalHomEvent_eq_ofFun` proves it equal to the direct stagewise description. -/
noncomputable def internalHomEvent (U : Ultrafilter ι) (F : SimpleGraph (Fin k))
    (G : ∀ i, SimpleGraph (X i)) : InternalRelation U X k :=
  (adjPairs F).inf fun e ↦
    InternalRelation.comap ![e.1, e.2] (internalEdgeRelation U G)

/-- A finite infimum of represented internal sets is represented by the pointwise finite
intersection.

`private`, by `Finset` induction over `InternalSet.top_def` and `InternalSet.inf_ofFun`.
Generic, but with a single consumer, so it stays here rather than enlarging the Boolean
API speculatively. -/
private theorem finset_inf_ofFun {Y : ι → Type*} {κ : Type*} (E : Finset κ)
    (f : κ → (i : ι) → Set (Y i)) :
    (E.inf fun e ↦ (Filter.Product.ofFun (f e) : InternalSet U Y))
      = Filter.Product.ofFun fun i ↦ ⋂ e ∈ E, f e i := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty, InternalSet.top_def]
    exact congrArg Filter.Product.ofFun (funext fun _ ↦ by simp)
  | insert a E ha ih =>
    rw [Finset.inf_insert, ih, InternalSet.inf_ofFun]
    exact congrArg Filter.Product.ofFun (funext fun _ ↦ by simp)

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

/-- **The direct stagewise description.**

The equality the module docstring promises: the intersection-of-pullbacks definition *is*
the internal set of stagewise edge-preserving tuples, as elements of `InternalRelation`
and not merely as sets with the same carrier.

Stated as an equality rather than as a carrier characterization on purpose. Without
nonempty fibers `InternalSet.carrier` is not known to be injective, so agreeing on
carriers would not give agreeing internal sets — and this module assumes no nonemptiness.

Everything here happens at the level of representative functions: the two sides are
literally equal as functions of the stage index, so the quotient step is `congrArg` and no
filter reasoning enters at all. -/
theorem internalHomEvent_eq_ofFun (F : SimpleGraph (Fin k))
    (G : ∀ i, SimpleGraph (X i)) :
    internalHomEvent U F G
      = Filter.Product.ofFun fun i ↦ homomorphismSet F (G i) := by
  rw [internalHomEvent, show (fun e : Fin k × Fin k ↦
      InternalRelation.comap ![e.1, e.2] (internalEdgeRelation U G))
    = fun e ↦ (Filter.Product.ofFun fun i ↦
        {p : Fin k → X i | (G i).Adj (p e.1) (p e.2)} : InternalRelation U X k) from ?_,
    finset_inf_ofFun]
  · refine congrArg Filter.Product.ofFun (funext fun i ↦ ?_)
    ext p
    simp only [Set.mem_iInter, Set.mem_setOf_eq, mem_adjPairs]
    exact ⟨fun h _ _ huv ↦ h ⟨_, _⟩ huv, fun h e he ↦ h he⟩
  · funext e
    rw [InternalRelation.comap, internalEdgeRelation, InternalSet.preimage_ofFun]
    rfl

/-- **The representative membership rule**, an immediate consequence of the equality: a
represented tuple family lies in the carrier exactly when it eventually preserves every
edge stagewise.

Note what this does *not* need — no commuting of the edge quantifier through `∀ᶠ`. The
finite intersection was already discharged at the representative level by
`internalHomEvent_eq_ofFun`, so this is just `InternalSet.mem_carrier_ofFun`. -/
@[simp]
theorem mem_carrier_internalHomEvent_ofFun (F : SimpleGraph (Fin k))
    (G : ∀ i, SimpleGraph (X i)) (p : (i : ι) → Fin k → X i) :
    (Filter.Product.ofFun p : Ultraproduct U fun i ↦ Fin k → X i)
        ∈ InternalSet.carrier (internalHomEvent U F G) ↔
      ∀ᶠ i in (U : Filter ι), ∀ ⦃u v⦄, F.Adj u v → (G i).Adj (p i u) (p i v) := by
  rw [internalHomEvent_eq_ofFun, InternalSet.mem_carrier_ofFun]
  rfl

/-- **The realized computation rule.**

A tuple of ultraproduct points lies in the realized event exactly when it is a graph
homomorphism into `ultraproductGraph U G` — stated as raw adjacency preservation, which is
what G3's counting will use.

This needs no **filter-level** finite-intersection argument — finiteness is still present
structurally, in `adjPairs` and the `Finset.inf` — because `tupleCarrier` is a preimage and
so takes the finite infimum to an intersection of sets, with no quantifier crossing a
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
