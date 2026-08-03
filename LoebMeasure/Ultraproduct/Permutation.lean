/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LoebMeasure.Ultraproduct.FinitePower
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Coordinate reindexing and the finite permutation action

Reindexing the coordinates of a filter product of function types, and the permutation
action as its special case.

Both are `Filter.Product.map`s, so they need no finiteness. The algebraic reindexing
laws derive from U2's functor laws, while compatibility with the finite-power
equivalences derives from U4's evaluation API. No fresh quotient arguments are needed.

The single law that drives the file is

```
eval a (reindex σ x) = eval (σ a) x
```

which is proved from U2's functor laws, not by quotient induction: the left-hand side
is a *nested* pair of `map`s and the right-hand side a single one, so `rfl` does not
apply — the obstruction is nesting, not the coordinate types, and it remains even when
`κ' = κ`. `map_map` closes the gap. Compatibility with `finitePiEquiv` then follows
from that plus `finitePiEquiv_apply`; `[Finite _]` appears only in statements that
mention the equivalence.

Nothing in this file performs representative elimination: the abstraction boundary
established by U1/U2 is genuinely sufficient here.

## The permutation action is contravariant

`permute σ` precomposes with `σ`, so it is a **pullback / right action**:

```
permute (σ * τ) = permute τ ∘ permute σ
```

This is the convention fixed by the D0.4 audit and recorded in the blueprint and
`ARCHITECTURE.md`; it is *not* the covariant `MulAction` convention, which would
precompose with `σ⁻¹`. `permute_mul` is deliberately a plain theorem rather than a simp
lemma, so that rewriting cannot silently pick an orientation.

## Main results

* `Filter.Product.reindex` with `eval_reindex`, `reindex_id`, `reindex_comp`, and
  `reindex_map` — reindexing commutes with a stagewise coordinate map.
* `Filter.Product.finitePiEquiv_reindex`: reindexing corresponds to precomposition of
  the transported family.
* `Filter.Product.permute` with `eval_permute`, `permute_one`, `permute_mul`,
  `permute_permute_symm`, `permute_map`, and `permute_zero`.
* `Filter.Product.finitePiEquiv_permute`, and the graded-facing `Fin` specializations
  `finPowerEquiv_reindex` and `finPowerEquiv_permute`.
* Inverse-facing companions — `reindex_finitePiEquiv_symm`,
  `permute_finitePiEquiv_symm`, and their `Fin` forms — so that goals about reindexing
  an *assembled* family make progress, not only goals about evaluating one.

Everything is generic in `l : Filter ι`: no ultrafilter and no countable-incompleteness
hypothesis, per ADR-0001.
-/

namespace Filter.Product

variable {ι : Type*} {l : Filter ι} {X : ι → Type*} {Y : ι → Type*}
  {κ : Type*} {κ' : Type*} {κ'' : Type*}

/-! ### Reindexing -/

/-- Reindex the coordinates of a filter product of function types along `σ`. This is a
coordinatewise `map`, so it needs no finiteness hypothesis. -/
def reindex (σ : κ' → κ) (x : l.Product fun i ↦ κ → X i) :
    l.Product fun i ↦ κ' → X i :=
  map (fun _ g ↦ g ∘ σ) x

@[simp]
theorem reindex_ofFun (σ : κ' → κ) (f : (i : ι) → κ → X i) :
    reindex σ (ofFun f : l.Product fun i ↦ κ → X i) = ofFun fun i ↦ f i ∘ σ :=
  rfl

/-- **The law that drives this file**: evaluating a reindexed product at `a` is
evaluating the original at `σ a`. Everything else about reindexing and permutation is
derived from this rather than from a fresh quotient argument. -/
@[simp]
theorem eval_reindex (σ : κ' → κ) (a : κ') (x : l.Product fun i ↦ κ → X i) :
    eval a (reindex σ x) = eval (σ a) x := by
  simp only [eval, reindex, map_map, Function.comp_def]

@[simp]
theorem reindex_id (x : l.Product fun i ↦ κ → X i) : reindex id x = x := by
  change map (fun _ : ι ↦ id) x = x
  exact map_id_apply x

/-- Reindexing is contravariantly functorial. -/
theorem reindex_comp (σ : κ' → κ) (τ : κ'' → κ') (x : l.Product fun i ↦ κ → X i) :
    reindex τ (reindex σ x) = reindex (σ ∘ τ) x := by
  simp only [reindex, map_map, Function.comp_def]

/-- Compatibility with the finite-product equivalence: reindexing corresponds to
precomposing the transported family. Derived from `eval_reindex` and
`finitePiEquiv_apply`, not from a fresh quotient argument. -/
theorem finitePiEquiv_reindex [Finite κ] [Finite κ'] (σ : κ' → κ)
    (x : l.Product fun i ↦ κ → X i) :
    finitePiEquiv (l := l) (X := X) κ' (reindex σ x)
      = fun a ↦ finitePiEquiv (l := l) (X := X) κ x (σ a) := by
  funext a
  rw [finitePiEquiv_apply, finitePiEquiv_apply, eval_reindex]

/-- Reindexing commutes with a stagewise map applied to coordinate values. Immediate
from `map_map`: both sides are the same pair of nested `map`s in the two orders. -/
@[simp]
theorem reindex_map (σ : κ' → κ) (f : (i : ι) → X i → Y i)
    (x : l.Product fun i ↦ κ → X i) :
    reindex σ (map (fun i (g : κ → X i) ↦ fun b ↦ f i (g b)) x)
      = map (fun i (g : κ' → X i) ↦ fun b ↦ f i (g b)) (reindex σ x) := by
  simp only [reindex, map_map, Function.comp_def]

/-! ### The permutation action

A right action, by the contravariance convention fixed in D0.4. -/

/-- The action of a permutation of the coordinate type, by precomposition. This is a
**pullback**, hence a right action: see `permute_mul`. -/
def permute (σ : Equiv.Perm κ) (x : l.Product fun i ↦ κ → X i) :
    l.Product fun i ↦ κ → X i :=
  reindex σ x

@[simp]
theorem permute_ofFun (σ : Equiv.Perm κ) (f : (i : ι) → κ → X i) :
    permute σ (ofFun f : l.Product fun i ↦ κ → X i) = ofFun fun i ↦ f i ∘ σ :=
  rfl

@[simp]
theorem eval_permute (σ : Equiv.Perm κ) (a : κ) (x : l.Product fun i ↦ κ → X i) :
    eval a (permute σ x) = eval (σ a) x :=
  eval_reindex σ a x

@[simp]
theorem permute_one (x : l.Product fun i ↦ κ → X i) :
    permute (1 : Equiv.Perm κ) x = x :=
  reindex_id x

/-- **Contravariance**: the order of `σ` and `τ` swaps. Deliberately not a simp lemma,
so that rewriting cannot silently pick an orientation. -/
theorem permute_mul (σ τ : Equiv.Perm κ) (x : l.Product fun i ↦ κ → X i) :
    permute (σ * τ) x = permute τ (permute σ x) := by
  simpa only [permute, Equiv.Perm.coe_mul] using
    (reindex_comp (l := l) (X := X) (σ : κ → κ) (τ : κ → κ) x).symm

@[simp]
theorem permute_permute_symm (σ : Equiv.Perm κ) (x : l.Product fun i ↦ κ → X i) :
    permute σ⁻¹ (permute σ x) = x := by
  rw [← permute_mul, mul_inv_cancel, permute_one]

@[simp]
theorem permute_symm_permute (σ : Equiv.Perm κ) (x : l.Product fun i ↦ κ → X i) :
    permute σ (permute σ⁻¹ x) = x := by
  rw [← permute_mul, inv_mul_cancel, permute_one]

/-- Compatibility of the permutation action with the finite-product equivalence. -/
theorem finitePiEquiv_permute [Finite κ] (σ : Equiv.Perm κ)
    (x : l.Product fun i ↦ κ → X i) :
    finitePiEquiv (l := l) (X := X) κ (permute σ x)
      = fun a ↦ finitePiEquiv (l := l) (X := X) κ x (σ a) :=
  finitePiEquiv_reindex σ x

/-- The permutation form of `reindex_map`. -/
@[simp]
theorem permute_map (σ : Equiv.Perm κ) (f : (i : ι) → X i → Y i)
    (x : l.Product fun i ↦ κ → X i) :
    permute σ (map (fun i (g : κ → X i) ↦ fun b ↦ f i (g b)) x)
      = map (fun i (g : κ → X i) ↦ fun b ↦ f i (g b)) (permute σ x) :=
  reindex_map (σ : κ → κ) f x

/-! ### Reindexing an assembled family

The inverse-facing companions of `eval_reindex`: reindexing a family that was assembled
from coordinates is the family precomposed with the reindexing. Safe as `simp` — they
rewrite an operation *surrounding* the inverse, not the equivalence itself. -/

/-- Reindexing an assembled family precomposes it.

Only `[Finite κ']` is needed: the proof injects through the *target* equivalence, and
the source coordinate type is never intersected over. `reindex_finitePiEquiv_symm`
below does need `[Finite κ]` as well, because its statement mentions the source
equivalence. -/
@[simp]
theorem reindex_finitePiMk [Finite κ'] (σ : κ' → κ) (F : κ → l.Product X) :
    reindex σ (finitePiMk F) = finitePiMk (F ∘ σ) := by
  refine (finitePiEquiv (l := l) (X := X) κ').injective (funext fun a ↦ ?_)
  rw [finitePiEquiv_apply, finitePiEquiv_apply, eval_reindex, eval_finitePiMk,
    eval_finitePiMk, Function.comp_apply]

/-- Reindexing through the inverse of the finite-product equivalence. -/
@[simp]
theorem reindex_finitePiEquiv_symm [Finite κ] [Finite κ'] (σ : κ' → κ)
    (F : κ → l.Product X) :
    reindex σ ((finitePiEquiv (l := l) (X := X) κ).symm F)
      = (finitePiEquiv (l := l) (X := X) κ').symm (F ∘ σ) := by
  rw [finitePiEquiv_symm_apply, finitePiEquiv_symm_apply, reindex_finitePiMk]

/-- The permutation form: permuting an assembled family precomposes it. -/
@[simp]
theorem permute_finitePiEquiv_symm [Finite κ] (σ : Equiv.Perm κ) (F : κ → l.Product X) :
    permute σ ((finitePiEquiv (l := l) (X := X) κ).symm F)
      = (finitePiEquiv (l := l) (X := X) κ).symm (F ∘ σ) :=
  reindex_finitePiEquiv_symm (σ : κ → κ) F

/-! ### `Fin` specializations

`finPowerEquiv` is an opaque `def`, so the generic theorems above do not by themselves
give the graded-facing API; these state it directly. Both are plain theorems rather than
`simp` lemmas, since they rewrite the whole equivalence. -/

/-- The `Fin`-power form of `finitePiEquiv_reindex`. -/
theorem finPowerEquiv_reindex {k k' : ℕ} (σ : Fin k' → Fin k)
    (x : l.Product fun i ↦ Fin k → X i) :
    finPowerEquiv (l := l) (X := X) k' (reindex σ x)
      = fun a ↦ finPowerEquiv (l := l) (X := X) k x (σ a) := by
  simpa only [finPowerEquiv_eq] using finitePiEquiv_reindex (l := l) (X := X) σ x

/-- The `Fin`-power form of `finitePiEquiv_permute`. -/
theorem finPowerEquiv_permute {k : ℕ} (σ : Equiv.Perm (Fin k))
    (x : l.Product fun i ↦ Fin k → X i) :
    finPowerEquiv (l := l) (X := X) k (permute σ x)
      = fun a ↦ finPowerEquiv (l := l) (X := X) k x (σ a) := by
  simpa only [finPowerEquiv_eq] using finitePiEquiv_permute (l := l) (X := X) σ x

/-- The `Fin`-power form of `reindex_finitePiEquiv_symm`. Safe as `simp` for the same
reason as the generic form — it rewrites an operation surrounding the inverse — and it
is *needed* separately because `finPowerEquiv` is opaque, so the generic lemma does not
match. -/
@[simp]
theorem reindex_finPowerEquiv_symm {k k' : ℕ} (σ : Fin k' → Fin k)
    (F : Fin k → l.Product X) :
    reindex σ ((finPowerEquiv (l := l) (X := X) k).symm F)
      = (finPowerEquiv (l := l) (X := X) k').symm (F ∘ σ) := by
  simpa only [finPowerEquiv_eq] using
    reindex_finitePiEquiv_symm (l := l) (X := X) σ F

/-- The `Fin`-power form of `permute_finitePiEquiv_symm`. -/
@[simp]
theorem permute_finPowerEquiv_symm {k : ℕ} (σ : Equiv.Perm (Fin k))
    (F : Fin k → l.Product X) :
    permute σ ((finPowerEquiv (l := l) (X := X) k).symm F)
      = (finPowerEquiv (l := l) (X := X) k).symm (F ∘ σ) := by
  simpa only [finPowerEquiv_eq] using
    permute_finitePiEquiv_symm (l := l) (X := X) σ F

/-- Degree zero is painless: every permutation of `Fin 0` acts trivially. -/
@[simp]
theorem permute_zero (σ : Equiv.Perm (Fin 0)) (x : l.Product fun i ↦ Fin 0 → X i) :
    permute σ x = x := by
  rw [Subsingleton.elim σ 1, permute_one]

/-! ### API tests -/

section Tests

/-- Reindexing computes on representatives. -/
example (σ : κ' → κ) (f : (i : ι) → κ → X i) :
    reindex σ (ofFun f : l.Product fun i ↦ κ → X i) = ofFun fun i ↦ f i ∘ σ := by simp

/-- The driving law, and its permutation form, by `simp`. -/
example (σ : κ' → κ) (a : κ') (x : l.Product fun i ↦ κ → X i) :
    eval a (reindex σ x) = eval (σ a) x := by simp

example (σ : Equiv.Perm κ) (a : κ) (x : l.Product fun i ↦ κ → X i) :
    eval a (permute σ x) = eval (σ a) x := by simp

/-- Identity and inverse cancellation are `simp`; composition is stated explicitly in
its contravariant form. -/
example (σ : Equiv.Perm κ) (x : l.Product fun i ↦ κ → X i) :
    permute σ⁻¹ (permute σ x) = x ∧ permute (1 : Equiv.Perm κ) x = x := by simp

example (σ τ : Equiv.Perm κ) (x : l.Product fun i ↦ κ → X i) :
    permute (σ * τ) x = permute τ (permute σ x) :=
  permute_mul σ τ x

/-- Compatibility with the equivalence, at a coordinate. -/
example [Finite κ] [Finite κ'] (σ : κ' → κ) (x : l.Product fun i ↦ κ → X i) (a : κ') :
    finitePiEquiv (l := l) (X := X) κ' (reindex σ x) a
      = finitePiEquiv (l := l) (X := X) κ x (σ a) := by
  simp

/-- The `Fin` specializations, which the graded layer will use directly. -/
example {k k' : ℕ} (σ : Fin k' → Fin k) (x : l.Product fun i ↦ Fin k → X i) (a : Fin k') :
    finPowerEquiv (l := l) (X := X) k' (reindex σ x) a
      = finPowerEquiv (l := l) (X := X) k x (σ a) := by
  rw [finPowerEquiv_reindex]

example {k : ℕ} (σ : Equiv.Perm (Fin k)) (x : l.Product fun i ↦ Fin k → X i) (a : Fin k) :
    finPowerEquiv (l := l) (X := X) k (permute σ x) a
      = finPowerEquiv (l := l) (X := X) k x (σ a) := by
  rw [finPowerEquiv_permute]

/-- Reindexing an assembled family precomposes it — the inverse-facing direction,
by `simp`. -/
example [Finite κ] [Finite κ'] (σ : κ' → κ) (F : κ → l.Product X) :
    reindex σ ((finitePiEquiv (l := l) (X := X) κ).symm F)
      = (finitePiEquiv (l := l) (X := X) κ').symm (F ∘ σ) := by
  simp

example {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Fin k → l.Product X) :
    permute σ ((finPowerEquiv (l := l) (X := X) k).symm F)
      = (finPowerEquiv (l := l) (X := X) k).symm (F ∘ σ) := by
  simp

/-- Reindexing commutes with a stagewise coordinate map, by `simp`. -/
example (σ : κ' → κ) (f : (i : ι) → X i → Y i) (x : l.Product fun i ↦ κ → X i) :
    reindex σ (map (fun i (g : κ → X i) ↦ fun b ↦ f i (g b)) x)
      = map (fun i (g : κ' → X i) ↦ fun b ↦ f i (g b)) (reindex σ x) := by
  simp

/-- Degree zero: every permutation acts trivially, by `simp`. -/
example (σ : Equiv.Perm (Fin 0)) (x : l.Product fun i ↦ Fin 0 → X i) :
    permute σ x = x := by simp

/-- **A genuine permutation example**: the swap on `Fin 3` exchanges the corresponding
coordinates of a `Fin 3`-power. -/
example (l : Filter ℕ) (X : ℕ → Type) (x : l.Product fun i ↦ Fin 3 → X i) :
    eval 0 (permute (Equiv.swap 0 1) x) = eval 1 x := by
  simp

/-- **Genuinely dependent fibers**. -/
example (l : Filter ℕ) (σ : Equiv.Perm (Fin 3)) (f : (i : ℕ) → Fin 3 → Fin (i + 1))
    (a : Fin 3) :
    eval a (permute σ (ofFun f : l.Product fun i ↦ Fin 3 → Fin (i + 1)))
      = ofFun fun i ↦ f i (σ a) := by
  simp

/-- **Independent universes** for the index type, the fibers, and both coordinate
types. -/
example {ι' : Type 2} {l' : Filter ι'} {X' : ι' → Type 5} {κ₁ : Type 7} {κ₂ : Type 3}
    (σ : κ₂ → κ₁) (f : (i : ι') → κ₁ → X' i) (a : κ₂) :
    eval a (reindex σ (ofFun f : l'.Product fun i ↦ κ₁ → X' i))
      = ofFun fun i ↦ f i (σ a) := by
  simp

end Tests

end Filter.Product
