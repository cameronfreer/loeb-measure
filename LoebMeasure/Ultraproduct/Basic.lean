/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Filter.Germ.Basic

/-!
# Representatives and induction for dependent filter products

`Filter.Product l ε` is mathlib's dependent quotient of `(i : ι) → ε i` by eventual
equality along `l`. At the pinned revision it carries almost no API: a `Setoid`, a
`CoeTC`, and an `Inhabited` instance. This module supplies the representative
vocabulary every downstream construction needs, mirroring `Filter.Germ`.

## The public constructor

`Filter.Product.ofFun` is the public way to build a product element from a dependent
function, and is the simp normal form. This is not merely cosmetic. Mathlib's
`Filter.Germ` instance is `⟨ofFun⟩`, so a `Germ` coercion elaborates to the stable head
symbol `Filter.Germ.ofFun`; but mathlib's `Filter.Product.coeTC` is
`⟨@Quotient.mk' _ (productSetoid _ ε)⟩`, so a `Product` coercion elaborates to
`Quotient.mk'` *with the setoid visible in the term*. Stating downstream simp lemmas
against that would expose the quotient implementation in every goal.

`ofFun` is therefore introduced with `@[coe]` — so it still displays as `↑f` — and the
raw quotient constructors are normalized into it by `quot_mk_eq_ofFun` and
`mk'_eq_ofFun`. Downstream modules should state lemmas in terms of `ofFun` and never
mention `Quotient.mk`, `Quotient.mk'`, `Quot.mk`, `Quotient.sound`, or `productSetoid`.

Upstreaming note: the tidy fix is a one-line mathlib change redefining `coeTC` as
`⟨ofFun⟩`, after which `mk'_eq_ofFun` becomes redundant. Until then the normalization
lemmas bridge the gap.

That decision also settles the naming. `Filter.Germ` names the analogous lemmas after
the coercion — `coe_eq`, `map_coe` — because its `coeTC` *is* `⟨ofFun⟩`. Ours are
`ofFun_eq_ofFun` and `map_ofFun`, naming the function that actually appears in the
terms. The two conventions converge exactly when `Product.coeTC` is routed through
`ofFun`; until then the `ofFun_*` names describe what a goal really contains, so the
naming question is *downstream of* the `coeTC` decision rather than independent of it.

## Main results

* `Filter.Product.ofFun`: the public constructor, and simp normal form.
* `Filter.Product.ofFun_eq_ofFun`: equality of represented products is *exactly*
  eventual equality of representatives.
* `Filter.Product.inductionOn`, `inductionOn₂`, `inductionOn₃`: representative
  elimination, marked `@[elab_as_elim]` following the `Filter.Germ` precedent.

Everything here is generic in `l : Filter ι`: there is no `Nonempty` fiber hypothesis,
no ultrafilter hypothesis, and no countable-incompleteness hypothesis. Those enter
strictly later, per ADR-0001.
-/

namespace Filter.Product

variable {ι : Type*} {l : Filter ι} {ε : ι → Type*} {δ : ι → Type*} {ζ : ι → Type*}

/-- The element of the filter product represented by a dependent function.

This is the public constructor and the simp normal form; downstream code should not
use `Quotient.mk'` or mention `Filter.productSetoid`. -/
@[coe]
def ofFun (f : (i : ι) → ε i) : l.Product ε :=
  @Quotient.mk' _ (productSetoid l ε) f

@[simp]
theorem quot_mk_eq_ofFun (f : (i : ι) → ε i) :
    Quot.mk _ f = (ofFun f : l.Product ε) :=
  rfl

@[simp]
theorem mk'_eq_ofFun (f : (i : ι) → ε i) :
    @Quotient.mk' _ (productSetoid l ε) f = ofFun f :=
  rfl

@[simp]
theorem mk_eq_ofFun (f : (i : ι) → ε i) :
    @Quotient.mk _ (productSetoid l ε) f = ofFun f :=
  rfl

/-- Every element of a filter product is represented by a dependent function. -/
theorem exists_ofFun (x : l.Product ε) : ∃ f : (i : ι) → ε i, x = ofFun f :=
  Quotient.inductionOn' x fun f ↦ ⟨f, rfl⟩

/-- **Equality of represented products is exactly eventual equality.** -/
@[simp]
theorem ofFun_eq_ofFun {f g : (i : ι) → ε i} :
    (ofFun f : l.Product ε) = ofFun g ↔ ∀ᶠ i in l, f i = g i :=
  Quotient.eq''

alias ⟨_, _root_.Filter.EventuallyEq.product_eq⟩ := ofFun_eq_ofFun

/-- Eventually equal representatives give the same product element. -/
theorem ofFun_congr {f g : (i : ι) → ε i} (h : ∀ᶠ i in l, f i = g i) :
    (ofFun f : l.Product ε) = ofFun g :=
  ofFun_eq_ofFun.2 h

/-- Representative elimination. Following the `Filter.Germ.inductionOn` precedent,
including `@[elab_as_elim]`. -/
@[elab_as_elim]
theorem inductionOn (x : l.Product ε) {motive : l.Product ε → Prop}
    (h : ∀ f : (i : ι) → ε i, motive (ofFun f)) : motive x :=
  Quotient.inductionOn' x h

@[elab_as_elim]
theorem inductionOn₂ (x : l.Product ε) (y : l.Product δ)
    {motive : l.Product ε → l.Product δ → Prop}
    (h : ∀ (f : (i : ι) → ε i) (g : (i : ι) → δ i), motive (ofFun f) (ofFun g)) :
    motive x y :=
  Quotient.inductionOn₂' x y h

@[elab_as_elim]
theorem inductionOn₃ (x : l.Product ε) (y : l.Product δ) (z : l.Product ζ)
    {motive : l.Product ε → l.Product δ → l.Product ζ → Prop}
    (h : ∀ (f : (i : ι) → ε i) (g : (i : ι) → δ i) (k : (i : ι) → ζ i),
      motive (ofFun f) (ofFun g) (ofFun k)) :
    motive x y z :=
  Quotient.inductionOn₃' x y z h

/-- Descend a function on representatives that respects eventual equality. Stated so
that downstream definitions never call `Quotient.liftOn` directly. -/
def liftOn {α : Sort*} (x : l.Product ε) (F : ((i : ι) → ε i) → α)
    (hF : ∀ f g : (i : ι) → ε i, (∀ᶠ i in l, f i = g i) → F f = F g) : α :=
  Quotient.liftOn' x F hF

@[simp]
theorem liftOn_ofFun {α : Sort*} (f : (i : ι) → ε i) (F : ((i : ι) → ε i) → α)
    (hF : ∀ f g : (i : ι) → ε i, (∀ᶠ i in l, f i = g i) → F f = F g) :
    liftOn (ofFun f : l.Product ε) F hF = F f :=
  rfl

/-! ### API tests

These check the properties the API is *for*, not just that it elaborates: that the
quotient implementation stays hidden, that the eliminators suffice, and that genuinely
dependent families over several universes work. -/

section Tests

/-- The mathlib coercion normalizes into `ofFun` by `simp`, so the setoid never
survives in a goal. -/
example (f : (i : ι) → ε i) : ((f : l.Product ε)) = ofFun f := by simp

/-- Equality is decided by eventual equality, with no `Quotient.sound` in sight. -/
example (f g : (i : ι) → ε i) (h : ∀ᶠ i in l, f i = g i) :
    (ofFun f : l.Product ε) = ofFun g := by simp [h]

/-- Elimination reaches a representative through the public API only. -/
example (x : l.Product ε) : ∃ f : (i : ι) → ε i, x = ofFun f := by
  induction x using Filter.Product.inductionOn with
  | _ f => exact ⟨f, rfl⟩

/-- Two-argument elimination. -/
example (x y : l.Product ε) (h : ∀ f g : (i : ι) → ε i,
    (ofFun f : l.Product ε) = ofFun g → ofFun g = (ofFun f : l.Product ε)) : x = y → y = x := by
  induction x, y using Filter.Product.inductionOn₂ with
  | _ f g => exact h f g

/-- A descent through `liftOn` computes on representatives, and its well-definedness
obligation genuinely consumes eventual equality — here discharged by `ofFun_congr`,
the pattern every content-like definition follows. -/
example (f : (i : ι) → ε i) :
    liftOn (ofFun f : l.Product ε)
      (fun g ↦ (ofFun g : l.Product ε))
      (fun _ _ h ↦ ofFun_congr h) =
      ofFun f := by
  simp

/-- **Genuinely dependent family**: the fibers vary with the index, so nothing here
collapses to the constant-type `Filter.Germ` case. -/
example (l : Filter ℕ) (f g : (i : ℕ) → Fin (i + 1)) (h : ∀ᶠ i in l, f i = g i) :
    (ofFun f : l.Product fun i ↦ Fin (i + 1)) = ofFun g := by
  simp [h]

/-- Dependent elimination over a varying family. -/
example (l : Filter ℕ) (x : l.Product fun i ↦ Fin (i + 1)) :
    ∃ f : (i : ℕ) → Fin (i + 1), x = ofFun f := by
  induction x using Filter.Product.inductionOn with
  | _ f => exact ⟨f, rfl⟩

/-- **Universe polymorphism**: the index type and the fibers live in independent
universes, and the fibers are not `Type 0`. -/
example {ι' : Type 2} {l' : Filter ι'} {ε' : ι' → Type 5} (f g : (i : ι') → ε' i)
    (h : ∀ᶠ i in l', f i = g i) : (ofFun f : l'.Product ε') = ofFun g := by
  simp [h]

end Tests

end Filter.Product
