# `LoebMeasure/Mathlib/` — upstream-oriented modules

Modules under this directory contain material that is **about mathlib objects only**:
no ultraproducts, no internal sets, no Loeb-specific notions. They exist here because
mathlib does not have them yet, and they are written so each can be proposed upstream
as an isolated pull request.

## Conventions

1. **Mirror the proposed mathlib path.** A module here sits at the path its upstream
   counterpart would occupy, so
   `LoebMeasure/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean` proposes
   additions to `Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`.
2. **Use mathlib namespaces**, never `Loeb`. Declarations must read exactly as they
   would upstream.
3. **Keep imports minimal.** Import the narrowest mathlib modules that suffice; never
   import a `Loeb`-specific module. This is what makes an isolated upstream PR
   possible, and it is checked by review rather than by tooling.
4. **No project-specific hypotheses.** If a statement needs a Loeb-specific notion, it
   belongs outside this directory.

Downstream `Loeb` modules import these freely. Nothing here may import downstream.

## Status

Upstreaming is tracked by issues labelled `kind: upstream`. Names may be bikeshedded
during upstream review; downstream code should therefore prefer wrapping these
declarations over duplicating their proofs, so a rename stays a one-line change.
