/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Ultralimits in compact spaces

Upstream-oriented material: these declarations concern only mathlib objects and live in
mathlib namespaces. See `LoebMeasure/Mathlib/README.md` for the mirror-path convention,
and issue #11 for the upstreaming proposal.

The probability-specific `ℝ≥0∞` results built on this — additivity, the bound by one,
and finiteness of a probability-valued ultralimit — are deliberately *not* here: they
are Loeb-specific specializations and belong outside the mirror.

`Ultrafilter.ultralimit U f` is the limit of `f` along `U`, defined as the limit of the
pushforward ultrafilter `U.map f`. In a compact codomain every function genuinely tends
to its ultralimit (`Ultrafilter.tendsto_ultralimit`); in a compact Hausdorff codomain
that limit is unique, which gives the computation rules.

The definition is total: it uses `Ultrafilter.lim`, which produces a junk value when
the filter has no limit, matching the `Filter.lim` idiom. Compactness is therefore a
hypothesis on the lemmas rather than on the definition.

## Main results

* `Ultrafilter.tendsto_ultralimit`: `Tendsto f U (𝓝 (U.ultralimit f))` in a compact
  space.
* `Ultrafilter.ultralimit_congr`: the ultralimit depends only on the `U`-germ of `f`.
* `Ultrafilter.ultralimit_const`, `Ultrafilter.ultralimit_comp`: computation rules in a
  compact Hausdorff space.
* `Ultrafilter.ultralimit_mono`, `Ultrafilter.ultralimit_le`,
  `Ultrafilter.le_ultralimit`: order rules in a compact space with an order-closed
  topology.
-/

namespace Ultrafilter

open Filter Topology

variable {ι K L : Type*} [TopologicalSpace K] [TopologicalSpace L]

/-- The limit of `f` along the ultrafilter `U`, defined as the limit of the pushforward
ultrafilter. Meaningful when the codomain is compact Hausdorff; junk otherwise. -/
noncomputable def ultralimit (U : Ultrafilter ι) (f : ι → K) : K :=
  (U.map f).lim

variable {U : Ultrafilter ι} {f g : ι → K}

/-- In a compact codomain, `f` genuinely tends to its ultralimit along `U`. -/
theorem tendsto_ultralimit [CompactSpace K] (U : Ultrafilter ι) (f : ι → K) :
    Tendsto f U (𝓝 (U.ultralimit f)) :=
  (U.map f).le_nhds_lim

/-- The ultralimit depends only on the `U`-germ of the function. -/
theorem ultralimit_congr (h : f =ᶠ[U] g) : U.ultralimit f = U.ultralimit g :=
  congrArg Ultrafilter.lim (Ultrafilter.coe_injective (map_congr h))

@[simp]
theorem ultralimit_const [CompactSpace K] [T2Space K] (c : K) :
    U.ultralimit (fun _ ↦ c) = c :=
  tendsto_nhds_unique (tendsto_ultralimit U _) tendsto_const_nhds

/-- Continuous maps commute with ultralimits. -/
theorem ultralimit_comp [CompactSpace K] [CompactSpace L] [T2Space L] {g : K → L}
    (hg : Continuous g) (U : Ultrafilter ι) (f : ι → K) :
    U.ultralimit (g ∘ f) = g (U.ultralimit f) :=
  tendsto_nhds_unique (tendsto_ultralimit U _) ((hg.tendsto _).comp (tendsto_ultralimit U f))

section Order

variable [CompactSpace K] [Preorder K] [OrderClosedTopology K]

/-- Ultralimits preserve eventual pointwise order. -/
theorem ultralimit_mono (h : ∀ᶠ i in U, f i ≤ g i) : U.ultralimit f ≤ U.ultralimit g :=
  le_of_tendsto_of_tendsto (tendsto_ultralimit U f) (tendsto_ultralimit U g) h

/-- Ultralimits preserve pointwise order. -/
theorem ultralimit_mono' (h : ∀ i, f i ≤ g i) : U.ultralimit f ≤ U.ultralimit g :=
  ultralimit_mono (Eventually.of_forall h)

/-- An eventual upper bound bounds the ultralimit. -/
theorem ultralimit_le {b : K} (h : ∀ᶠ i in U, f i ≤ b) : U.ultralimit f ≤ b :=
  le_of_tendsto (tendsto_ultralimit U f) h

/-- An eventual lower bound bounds the ultralimit from below. -/
theorem le_ultralimit {b : K} (h : ∀ᶠ i in U, b ≤ f i) : b ≤ U.ultralimit f :=
  ge_of_tendsto (tendsto_ultralimit U f) h

end Order

end Ultrafilter
