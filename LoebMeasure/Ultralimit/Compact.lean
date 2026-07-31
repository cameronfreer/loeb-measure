/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact ultralimits

D0.2 spike (issue #2, ADR-0002): the limit of a function along an ultrafilter, defined
via `Ultrafilter.lim`. In a compact codomain every function genuinely tends to its
ultralimit; in a compact Hausdorff codomain that limit is unique, which gives the
computation rules below.

Declaration names are provisional until ADR-0002 is accepted.
-/

namespace Loeb

open Filter Topology

variable {ι K L : Type*} [TopologicalSpace K] [TopologicalSpace L]

/-- The limit of `f` along the ultrafilter `U`. Meaningful when the codomain is a
compact Hausdorff space; junk otherwise. -/
noncomputable def ultralimit (U : Ultrafilter ι) (f : ι → K) : K :=
  (U.map f).lim

variable {U : Ultrafilter ι} {f g : ι → K}

/-- In a compact codomain, `f` genuinely tends to its ultralimit along `U`. -/
theorem tendsto_ultralimit [CompactSpace K] (U : Ultrafilter ι) (f : ι → K) :
    Tendsto f U (𝓝 (ultralimit U f)) :=
  (U.map f).le_nhds_lim

/-- The ultralimit depends only on the `U`-germ of the function. -/
theorem ultralimit_congr (h : f =ᶠ[U] g) : ultralimit U f = ultralimit U g :=
  congrArg Ultrafilter.lim (Ultrafilter.coe_injective (map_congr h))

@[simp]
theorem ultralimit_const [CompactSpace K] [T2Space K] (c : K) :
    ultralimit U (fun _ ↦ c) = c :=
  tendsto_nhds_unique (tendsto_ultralimit U _) tendsto_const_nhds

/-- Continuous maps commute with ultralimits. -/
theorem ultralimit_comp [CompactSpace K] [CompactSpace L] [T2Space L] {g : K → L}
    (hg : Continuous g) (U : Ultrafilter ι) (f : ι → K) :
    ultralimit U (g ∘ f) = g (ultralimit U f) :=
  tendsto_nhds_unique (tendsto_ultralimit U _) ((hg.tendsto _).comp (tendsto_ultralimit U f))

section Order

variable [CompactSpace K] [Preorder K] [OrderClosedTopology K]

/-- Ultralimits preserve eventual pointwise order. -/
theorem ultralimit_mono (h : ∀ᶠ i in U, f i ≤ g i) : ultralimit U f ≤ ultralimit U g :=
  le_of_tendsto_of_tendsto (tendsto_ultralimit U f) (tendsto_ultralimit U g) h

/-- Ultralimits preserve pointwise order. -/
theorem ultralimit_mono' (h : ∀ i, f i ≤ g i) : ultralimit U f ≤ ultralimit U g :=
  ultralimit_mono (Eventually.of_forall h)

/-- An eventual upper bound bounds the ultralimit. -/
theorem ultralimit_le {b : K} (h : ∀ᶠ i in U, f i ≤ b) : ultralimit U f ≤ b :=
  le_of_tendsto (tendsto_ultralimit U f) h

/-- An eventual lower bound bounds the ultralimit from below. -/
theorem le_ultralimit {b : K} (h : ∀ᶠ i in U, b ≤ f i) : b ≤ ultralimit U f :=
  ge_of_tendsto (tendsto_ultralimit U f) h

end Order

end Loeb
