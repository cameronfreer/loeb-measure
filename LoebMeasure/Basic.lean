/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# Loeb measure

Scaffolding module for the `LoebMeasure` library. The placeholder below exists only so
the root import spine, the build, and CI are exercised from the first commit; it is
expected to be replaced by the first real unit.

Declarations in this library live principally in the `Loeb` namespace.
-/

namespace Loeb

/-- An ultrafilter decides every set: for any set `s`, either `s` or its complement is
large. Placeholder declaration for the initial scaffold. -/
theorem mem_or_compl_mem {α : Type*} (U : Ultrafilter α) (s : Set α) : s ∈ U ∨ sᶜ ∈ U :=
  U.mem_or_compl_mem s

end Loeb
