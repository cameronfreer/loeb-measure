/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.Order.Compact

/-!
# Ultralimits in compact spaces

Upstream-oriented material: these declarations concern only mathlib objects and live in
mathlib namespaces. See `LoebMeasure/Mathlib/README.md` for the mirror-path convention,
and issue #11 for the upstreaming proposal.

The probability-specific `ℝ≥0∞` results built on this — additivity, the bound by one,
and finiteness of a probability-valued ultralimit — are deliberately *not* here: they
are Loeb-specific specializations and belong outside the mirror.

`Ultrafilter.ultralimit U f` is the limit of `f` along `U`, defined as the limit of the
pushforward ultrafilter `U.map f`. It agrees with a unique limit whenever one exists;
compactness is what guarantees that a limit exists for *every* function
(`Ultrafilter.tendsto_ultralimit`).

The definition is total: it uses `Ultrafilter.lim`, which produces a junk value when
the filter has no limit, matching the `Filter.lim` idiom. Hypotheses therefore sit on
the lemmas, and each takes only what it needs — a constant's ultralimit needs
uniqueness but no compactness, and composition needs compactness only on the source.

## Main results

* `Ultrafilter.tendsto_ultralimit`: `Tendsto f U (𝓝 (U.ultralimit f))` in a compact
  space.
* `Ultrafilter.tendsto_ultralimit_of_eventually_mem_compact`: the same conclusion from
  eventual containment in a compact *set*, with no hypothesis on the ambient space at all.
* `Ultrafilter.ultralimit_congr`: the ultralimit depends only on the `U`-germ of `f`.
* `Ultrafilter.ultralimit_const`, `Ultrafilter.ultralimit_comp`: computation rules in a
  compact Hausdorff space.
* `Ultrafilter.ultralimit_mono`, `Ultrafilter.ultralimit_le`,
  `Ultrafilter.le_ultralimit`: order rules in a compact space with an order-closed
  topology.
* `Ultrafilter.ultralimit_eq_limUnder`: the bridge to `Filter.limUnder`, which the two
  share definitionally when `K` is nonempty.

Hypotheses are kept exact: `ultralimit_const` needs only `[T2Space K]`, and
`ultralimit_comp` only `[CompactSpace K] [T2Space L]` — compactness of the *target* is
not required.
-/

namespace Ultrafilter

open Filter Topology

variable {ι K L : Type*} [TopologicalSpace K] [TopologicalSpace L]

/-- The limit of `f` along the ultrafilter `U`, defined as the limit of the pushforward
ultrafilter.

Meaningful whenever the pushed-forward ultrafilter has a limit at all, and junk otherwise.
A compact Hausdorff codomain is the convenient sufficient condition — it makes the limit
exist and be unique — but it is not necessary:
`tendsto_ultralimit_of_eventually_mem_compact` shows that eventual containment in a compact
*set* already makes this a genuine limit, under no hypothesis on the space at all. -/
noncomputable def ultralimit (U : Ultrafilter ι) (f : ι → K) : K :=
  (U.map f).lim

variable {U : Ultrafilter ι} {f g : ι → K}

/-- **Relationship to `Filter.limUnder`.** This is not a missing limit construction but
an ergonomic specialization: `Ultrafilter.lim` derives the `Nonempty` instance from the
mapped ultrafilter, which `Filter.limUnder` must be given. Where the instance is
available anyway the two agree definitionally. -/
theorem ultralimit_eq_limUnder [Nonempty K] (U : Ultrafilter ι) (f : ι → K) :
    U.ultralimit f = Filter.limUnder (U : Filter ι) f :=
  rfl

/-- In a compact codomain, `f` genuinely tends to its ultralimit along `U`. -/
theorem tendsto_ultralimit [CompactSpace K] (U : Ultrafilter ι) (f : ι → K) :
    Tendsto f U (𝓝 (U.ultralimit f)) :=
  (U.map f).le_nhds_lim

/-- **Eventual containment in a compact set suffices.**

The ambient space need be neither compact nor Hausdorff: compactness of `s` supplies a
cluster point of the pushed-forward ultrafilter, which for an ultrafilter *is* a limit, and
`le_nhds_lim` then names it.

What Hausdorffness would supply is **uniqueness** of that limit — and, together with
compactness, closedness of `s`. Neither is wanted here: the conclusion is about the
particular point `U.ultralimit f`, which the definition already names, and membership of an
*already closed* set passes to a limit without any separation hypothesis.

This is what makes the ultralimit usable on `ℝ`, which is not compact. -/
theorem tendsto_ultralimit_of_eventually_mem_compact {s : Set K} (hs : IsCompact s)
    (h : ∀ᶠ i in U, f i ∈ s) : Tendsto f U (𝓝 (U.ultralimit f)) := by
  have hle : ((U.map f : Ultrafilter K) : Filter K) ≤ Filter.principal s := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff]
    exact h
  obtain ⟨x, -, hx⟩ := hs.ultrafilter_le_nhds (U.map f) hle
  exact _root_.le_nhds_lim ⟨x, hx⟩

/-- The ultralimit depends only on the `U`-germ of the function. -/
theorem ultralimit_congr (h : f =ᶠ[U] g) : U.ultralimit f = U.ultralimit g :=
  congrArg Ultrafilter.lim (Ultrafilter.coe_injective (map_congr h))

@[simp]
theorem ultralimit_const [T2Space K] (c : K) : U.ultralimit (fun _ ↦ c) = c := by
  have h : ((U.map fun _ ↦ c : Ultrafilter K) : Filter K) ≤ 𝓝 c := by
    rw [Ultrafilter.coe_map, Filter.map_const]
    exact pure_le_nhds c
  exact lim_eq h

/-- Continuous maps commute with ultralimits. -/
theorem ultralimit_comp [CompactSpace K] [T2Space L] {g : K → L}
    (hg : Continuous g) (U : Ultrafilter ι) (f : ι → K) :
    U.ultralimit (g ∘ f) = g (U.ultralimit f) := by
  have h : ((U.map (g ∘ f) : Ultrafilter L) : Filter L) ≤ 𝓝 (g (U.ultralimit f)) := by
    rw [Ultrafilter.coe_map]
    exact (hg.tendsto _).comp (tendsto_ultralimit U f)
  exact lim_eq h

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
