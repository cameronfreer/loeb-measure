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

Both are `Filter.Product.map`s, so they need no finiteness, and everything about them
is derived from the evaluation and naturality laws of
`LoebMeasure/Ultraproduct/FinitePower.lean` rather than from fresh quotient arguments.
The single law that drives the file is

```
eval a (reindex σ x) = eval (σ a) x
```

whose proof is a single representative elimination — both sides are the same
coordinatewise `map`, but at different universe instantiations of `eval`, so `rfl`
alone does not typecheck. Compatibility with `finitePiEquiv` then follows from that
plus `finitePiEquiv_apply`; `[Finite _]` appears only in statements that mention the
equivalence.

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

* `Filter.Product.reindex` with `eval_reindex`, `reindex_id`, `reindex_comp`.
* `Filter.Product.finitePiEquiv_reindex`: reindexing corresponds to precomposition of
  the transported family.
* `Filter.Product.permute` with `eval_permute`, `permute_one`, `permute_mul`,
  `permute_permute_symm`.

Everything is generic in `l : Filter ι`: no ultrafilter and no countable-incompleteness
hypothesis, per ADR-0001.
-/

namespace Filter.Product

variable {ι : Type*} {l : Filter ι} {X : ι → Type*} {κ : Type*} {κ' : Type*} {κ'' : Type*}

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
  induction x using Filter.Product.inductionOn with
  | _ f => rfl

@[simp]
theorem reindex_id (x : l.Product fun i ↦ κ → X i) : reindex id x = x := by
  induction x using Filter.Product.inductionOn with
  | _ f => rfl

/-- Reindexing is contravariantly functorial. -/
theorem reindex_comp (σ : κ' → κ) (τ : κ'' → κ') (x : l.Product fun i ↦ κ → X i) :
    reindex τ (reindex σ x) = reindex (σ ∘ τ) x := by
  induction x using Filter.Product.inductionOn with
  | _ f => rfl

/-- Compatibility with the finite-product equivalence: reindexing corresponds to
precomposing the transported family. Derived from `eval_reindex` and
`finitePiEquiv_apply`, not from a fresh quotient argument. -/
theorem finitePiEquiv_reindex [Finite κ] [Finite κ'] (σ : κ' → κ)
    (x : l.Product fun i ↦ κ → X i) :
    finitePiEquiv (l := l) (X := X) κ' (reindex σ x)
      = fun a ↦ finitePiEquiv (l := l) (X := X) κ x (σ a) := by
  funext a
  rw [finitePiEquiv_apply, finitePiEquiv_apply, eval_reindex]

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
  induction x using Filter.Product.inductionOn with
  | _ f => rfl

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
