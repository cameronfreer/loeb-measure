/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Ultraproduct.Prod
import Mathlib.Order.Filter.Finite

/-!
# Finite dependent-product and `Fin`-power equivalences

A filter product of *finitely* many stagewise coordinates is a finite family of filter
products:

```
l.Product (fun i ↦ κ → X i)      ≃ (κ → l.Product X)      -- [Finite κ]
l.Product (fun i ↦ Fin k → X i)  ≃ (Fin k → l.Product X)
```

These are the equivalences the graded layer rests on: measure theory happens on the
`l.Product (fun i ↦ Fin k → X i)` side, where sets are internal, and is transported to
`Fin k → l.Product X` only at API boundaries.

## Where finiteness is needed, and where it is not

Finiteness is needed more narrowly than one might expect, and the API records exactly
where:

* `Filter.Product.eval`, the forward direction, is a coordinatewise `map` — no
  finiteness, stated for arbitrary `κ`.
* `Filter.Product.finitePiMk`, the assembling direction, **also needs no finiteness**:
  it chooses a representative per coordinate and transposes. Both it and
  `eval_finitePiMk` (the right inverse) are stated for arbitrary `κ`.
* Finiteness is consumed by exactly one theorem: `finitePiMk_ofFun`, the **left**
  inverse. Recovering the original element requires knowing that the per-coordinate
  choices agree with it *simultaneously*, which intersects a `κ`-indexed family of
  eventual-equality sets — and a filter is closed under finite intersections only.

That single step is isolated in `eventually_forall_of_forall`, the one place in this
file where `Filter.eventually_all` is used, so the argument is auditable in one spot.

This is the genuine difficulty U3's binary case did not have: there the two
representative changes were discharged sequentially by nested `liftOn`, with no
intersection at all.

Note that `[Finite κ]` is a `Prop`-valued typeclass and never a `[Fintype κ]`: nothing
here needs to enumerate `κ`.

## Main results

* `Filter.Product.eval`: evaluation at a coordinate, needing no finiteness.
* `Filter.Product.finitePiEquiv`: the equivalence, for `[Finite κ]`.
* `Filter.Product.finPowerEquiv`: the `κ := Fin k` specialization, *definitionally* so.
* `Filter.Product.finitePiEquiv_apply`, `finitePiEquiv_symm_ofFun`: computation rules.
* `Filter.Product.eval_finitePiEquiv_symm`, `eval_finPowerEquiv_symm`: the
  inverse-facing evaluation rules — the coordinates of an assembled family are the
  family. These are what make downstream goals about `(…).symm F` progress.
* `Filter.Product.map_finitePiEquiv_symm`: naturality against `Filter.Product.map`.

Compatibility of these equivalences with coordinate reindexing and with permutation
actions is deliberately **not** here: those are U5, and are derived from the evaluation
and naturality laws below. This module does not depend on U5.

Compatibility with the canonical coordinate split is likewise absent: the `splitEquiv`
wrapper around `Fin.appendEquiv` fixed by the D0.4 audit has not yet reached `main`,
so split compatibility follows whenever that wrapper is promoted.

Everything is generic in `l : Filter ι`: no ultrafilter and no countable-incompleteness
hypothesis, per ADR-0001.
-/

namespace Filter.Product

variable {ι : Type*} {l : Filter ι} {X : ι → Type*} {Y : ι → Type*} {κ : Type*}

/-! ### Evaluation: the forward direction, finiteness-free -/

/-- Evaluation of a filter product of functions at a coordinate. This is a
coordinatewise `map`, so it needs no finiteness hypothesis. -/
def eval (a : κ) (x : l.Product fun i ↦ κ → X i) : l.Product X :=
  map (fun _ g ↦ g a) x

@[simp]
theorem eval_ofFun (a : κ) (f : (i : ι) → κ → X i) :
    eval a (ofFun f : l.Product fun i ↦ κ → X i) = ofFun fun i ↦ f i a :=
  rfl

/-! ### The finite-intersection step

This is the only place in the file where finiteness is consumed. -/

/-- Pointwise eventual statements over a **finite** index type can be gathered into a
single eventual statement. This is the one step requiring `[Finite κ]`: a filter is
closed under finite intersections only.

`private`, and deliberately so: it is just one direction of the existing
`Filter.eventually_all`, carries no filter-product content, and does not belong in the
`Filter.Product` namespace as public API. It exists only to give the finiteness step a
single auditable name. -/
private theorem eventually_forall_of_forall [Finite κ] {p : κ → ι → Prop}
    (h : ∀ a, ∀ᶠ i in l, p a i) : ∀ᶠ i in l, ∀ a, p a i :=
  Filter.eventually_all.2 h

/-- A choice of representative for each coordinate. -/
private noncomputable def rep (F : κ → l.Product X) (a : κ) : (i : ι) → X i :=
  Classical.choose (exists_ofFun (F a))

private theorem ofFun_rep (F : κ → l.Product X) (a : κ) : ofFun (rep F a) = F a :=
  (Classical.choose_spec (exists_ofFun (F a))).symm

/-- Assemble a family of filter products into a filter product of functions, by
choosing a representative for each coordinate and transposing.

No finiteness is needed to *build* this, nor to prove `eval_finitePiMk`; the choices
only have to be reconciled with each other in `finitePiMk_ofFun`, which is where
`[Finite κ]` is consumed. -/
noncomputable def finitePiMk (F : κ → l.Product X) :
    l.Product fun i ↦ κ → X i :=
  ofFun fun i a ↦ rep F a i

@[simp]
theorem eval_finitePiMk (F : κ → l.Product X) (a : κ) :
    eval a (finitePiMk F) = F a := by
  rw [finitePiMk, eval_ofFun]
  exact ofFun_rep F a

theorem finitePiMk_ofFun [Finite κ] (f : (i : ι) → κ → X i) :
    finitePiMk (fun a ↦ (ofFun fun i ↦ f i a : l.Product X)) = ofFun f := by
  refine ofFun_congr ?_
  refine (eventually_forall_of_forall fun a ↦ ?_).mono fun i hi ↦ funext fun a ↦ hi a
  exact ofFun_eq_ofFun.1 (ofFun_rep (fun a ↦ (ofFun fun i ↦ f i a : l.Product X)) a)

/-! ### The equivalences -/

/-- The finite dependent-product equivalence. Simp discipline follows U3: the normal
form computes on representatives and coordinates, and round-trips are left to the
generic `Equiv.symm_apply_apply`/`apply_symm_apply`; no lemma rewriting the equivalence
*as a whole* on an arbitrary element is `simp`. -/
noncomputable def finitePiEquiv (κ : Type*) [Finite κ] :
    (l.Product fun i ↦ κ → X i) ≃ (κ → l.Product X) where
  toFun x a := eval a x
  invFun := finitePiMk
  left_inv x := by
    induction x using Filter.Product.inductionOn with
    | _ f => simpa using finitePiMk_ofFun f
  right_inv F := by
    funext a
    simp

/-- Coordinates of the forward map are evaluations. Safe as `simp`: it rewrites a
coordinate, not the equivalence itself. -/
@[simp]
theorem finitePiEquiv_apply [Finite κ] (x : l.Product fun i ↦ κ → X i) (a : κ) :
    finitePiEquiv (l := l) (X := X) κ x a = eval a x :=
  rfl

/-- Deliberately **not** `simp`: it rewrites the inverse *as a whole* on an arbitrary
element, which would pre-empt `Equiv.apply_symm_apply` and leave round-trip goals
stuck. This is the same hazard as in `Prod.lean`; only coordinate/evaluation lemmas are
safe to mark. -/
theorem finitePiEquiv_symm_apply [Finite κ] (F : κ → l.Product X) :
    (finitePiEquiv (l := l) (X := X) κ).symm F = finitePiMk F :=
  rfl

/-- The `Fin`-power equivalence: **definitionally** the `κ := Fin k` specialization,
not an independent construction. -/
noncomputable def finPowerEquiv (k : ℕ) :
    (l.Product fun i ↦ Fin k → X i) ≃ (Fin k → l.Product X) :=
  finitePiEquiv (Fin k)

theorem finPowerEquiv_eq (k : ℕ) :
    finPowerEquiv (l := l) (X := X) k = finitePiEquiv (Fin k) :=
  rfl

@[simp]
theorem finPowerEquiv_apply (k : ℕ) (x : l.Product fun i ↦ Fin k → X i) (j : Fin k) :
    finPowerEquiv (l := l) (X := X) k x j = eval j x :=
  rfl

/-- Not `simp`, for the same reason as `finitePiEquiv_symm_apply`. -/
theorem finPowerEquiv_symm_apply (k : ℕ) (F : Fin k → l.Product X) :
    (finPowerEquiv (l := l) (X := X) k).symm F = finitePiMk F :=
  rfl

/-- The inverse, computed on a **representative-shaped** family. Safe as `simp`,
unlike `finitePiEquiv_symm_apply`: the left-hand side matches only a family that is
already given coordinatewise by representatives, so it cannot fire on the arbitrary
element of a round-trip goal. -/
@[simp]
theorem finitePiEquiv_symm_ofFun [Finite κ] (f : (i : ι) → κ → X i) :
    (finitePiEquiv (l := l) (X := X) κ).symm (fun a ↦ (ofFun fun i ↦ f i a : l.Product X))
      = ofFun f := by
  rw [finitePiEquiv_symm_apply]
  exact finitePiMk_ofFun f

/-- Evaluating a coordinate of the inverse recovers that coordinate. Safe as `simp` in
the U3 sense: it rewrites a coordinate, not the equivalence itself, so round-trip goals
are unaffected. -/
@[simp]
theorem eval_finitePiEquiv_symm [Finite κ] (F : κ → l.Product X) (a : κ) :
    eval a ((finitePiEquiv (l := l) (X := X) κ).symm F) = F a := by
  rw [finitePiEquiv_symm_apply, eval_finitePiMk]

/-- The `Fin`-power form of `eval_finitePiEquiv_symm`. -/
@[simp]
theorem eval_finPowerEquiv_symm (k : ℕ) (F : Fin k → l.Product X) (j : Fin k) :
    eval j ((finPowerEquiv (l := l) (X := X) k).symm F) = F j := by
  rw [finPowerEquiv_symm_apply, eval_finitePiMk]

/-! ### Naturality

The generic laws from which U5 will derive reindexing and permutation compatibility.
U5's named theorems are deliberately not stated here. -/

/-- Evaluation commutes with a stagewise map applied coordinatewise. -/
@[simp]
theorem eval_map (f : (i : ι) → X i → Y i) (a : κ)
    (x : l.Product fun i ↦ κ → X i) :
    eval a (map (fun i (g : κ → X i) ↦ fun b ↦ f i (g b)) x) = map f (eval a x) := by
  induction x using Filter.Product.inductionOn with
  | _ g => simp

/-- Naturality of the inverse against `map`. -/
@[simp]
theorem map_finitePiMk [Finite κ] (f : (i : ι) → X i → Y i) (F : κ → l.Product X) :
    map (fun i (g : κ → X i) ↦ fun b ↦ f i (g b)) (finitePiMk F)
      = finitePiMk fun a ↦ map f (F a) := by
  refine (finitePiEquiv (l := l) (X := Y) κ).injective (funext fun a ↦ ?_)
  rw [finitePiEquiv_apply, finitePiEquiv_apply, eval_map, eval_finitePiMk, eval_finitePiMk]

/-- Naturality in equivalence form, the interface downstream code should use: it never
mentions `finitePiMk`, so the representative choice stays hidden behind the equivalence
API. -/
@[simp]
theorem map_finitePiEquiv_symm [Finite κ] (f : (i : ι) → X i → Y i)
    (F : κ → l.Product X) :
    map (fun i (g : κ → X i) ↦ fun b ↦ f i (g b))
        ((finitePiEquiv (l := l) (X := X) κ).symm F)
      = (finitePiEquiv (l := l) (X := Y) κ).symm fun a ↦ map f (F a) := by
  rw [finitePiEquiv_symm_apply, finitePiEquiv_symm_apply]
  exact map_finitePiMk f F

/-! ### Degree zero and one -/

/-- Degree zero is painless: the product over an empty coordinate type is a subsingleton
and the equivalence is trivially determined. -/
@[simp]
theorem finPowerEquiv_zero (x : l.Product fun i ↦ Fin 0 → X i) :
    finPowerEquiv (l := l) (X := X) 0 x = Fin.elim0 := by
  funext j
  exact j.elim0

/-- Degree one: the single coordinate is evaluation at `0`. -/
theorem finPowerEquiv_one (x : l.Product fun i ↦ Fin 1 → X i) :
    finPowerEquiv (l := l) (X := X) 1 x 0 = eval 0 x :=
  rfl

/-! ### API tests -/

section Tests

/-- Evaluation computes on representatives; no finiteness is involved. -/
example (f : (i : ι) → κ → X i) (a : κ) :
    eval a (ofFun f : l.Product fun i ↦ κ → X i) = ofFun fun i ↦ f i a := by simp

/-- The inverse computes on representatives, by `simp` alone. -/
example [Finite κ] (f : (i : ι) → κ → X i) :
    (finitePiEquiv (l := l) (X := X) κ).symm (fun a ↦ ofFun fun i ↦ f i a) = ofFun f := by
  simp

/-- The inverse-facing evaluation rules: coordinates of an assembled family are the
family, by `simp`. These are the goals downstream code actually meets. -/
example [Finite κ] (F : κ → l.Product X) (a : κ) :
    eval a ((finitePiEquiv (l := l) (X := X) κ).symm F) = F a := by simp

example (k : ℕ) (F : Fin k → l.Product X) (j : Fin k) :
    eval j ((finPowerEquiv (l := l) (X := X) k).symm F) = F j := by simp

/-- **Round-trips close through the generic `Equiv` simp lemmas**, on arbitrary
elements, as the U3 discipline requires. -/
example [Finite κ] (x : l.Product fun i ↦ κ → X i) :
    (finitePiEquiv (l := l) (X := X) κ).symm (finitePiEquiv κ x) = x := by simp

example [Finite κ] (F : κ → l.Product X) :
    finitePiEquiv (l := l) (X := X) κ ((finitePiEquiv κ).symm F) = F := by simp

/-- The `Fin`-power case is the specialization, by `rfl`. -/
example (k : ℕ) :
    finPowerEquiv (l := l) (X := X) k = finitePiEquiv (Fin k) := rfl

/-- **Successor degree**: coordinates of a `Fin (k+1)`-power are evaluations, including
at the last coordinate. -/
example (k : ℕ) (f : (i : ι) → Fin (k + 1) → X i) (j : Fin (k + 1)) :
    finPowerEquiv (l := l) (X := X) (k + 1) (ofFun f) j = ofFun fun i ↦ f i j := by
  simp

/-- **Genuinely dependent fibers**, with the coordinate type finite. -/
example (l : Filter ℕ) (f : (i : ℕ) → Fin 3 → Fin (i + 1)) (j : Fin 3) :
    finPowerEquiv (l := l) (X := fun i ↦ Fin (i + 1)) 3 (ofFun f) j
      = ofFun fun i ↦ f i j := by
  simp

/-- **Independent universes** for the index type, the fibers, and the coordinate type. -/
example {ι' : Type 2} {l' : Filter ι'} {X' : ι' → Type 5} {κ' : Type 7} [Finite κ']
    (f : (i : ι') → κ' → X' i) (a : κ') :
    finitePiEquiv (l := l') (X := X') κ' (ofFun f) a = ofFun fun i ↦ f i a := by
  simp

/-- Naturality is usable without naming `finitePiMk`. -/
example [Finite κ] (f : (i : ι) → X i → Y i) (F : κ → l.Product X) :
    map (fun i (g : κ → X i) ↦ fun b ↦ f i (g b))
        ((finitePiEquiv (l := l) (X := X) κ).symm F)
      = (finitePiEquiv (l := l) (X := Y) κ).symm fun a ↦ map f (F a) := by
  simp

end Tests

end Filter.Product
