# ADR-0004 — General measured families versus counting spaces

Status: Accepted

Date: 2026-08-15

Issue: activated by the M3 content unit (C2); deferred at M0 as open decision 4

## Context

The M0 review deferred this question with an explicit trigger: *activate before M3*.
That trigger has arrived. L1, L2, and C1 did not commit the choice — none of them
mentions a stage measure — but the internal content does, since its very signature
either takes a stage-measure parameter or does not.

The question: should the first Loeb construction be built for **normalized counting on
finite discrete stages**, or immediately for a **general family of measured stages**?

## Constraints

- ARCHITECTURE records that the first concrete model is normalized finite counting
  measure, and that general families "are not allowed to complicate the first
  construction unless a design spike shows the general API is no harder".
- The blueprint's Layer I caveat records that `InternalSet` quantifies over **all**
  stagewise subsets, and that general measured families would add a separate
  `InternalMeasurableSet` with a forgetful map — putting the generalization cost in the
  *content's domain*, not in the internal-set layer.
- Hoover needs genuinely varying probability spaces eventually; Elek–Szegedy needs only
  finite counting stages.

## Evidence

A signature spike compared the two directly. Both elaborate, so feasibility does not
decide it; the consequences do.

```lean
-- A, counting-first: the content is a function of the internal set alone.
def contentA [∀ i, Fintype (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (U : Ultrafilter ι) (A : InternalSet U X) : ℝ≥0∞

-- B, general: the content takes a stage-measure parameter.
def contentB (U : Ultrafilter ι) (μ : ∀ i, Measure (X i)) (A : InternalSet U X) : ℝ≥0∞
```

What the spike showed:

1. **B's definition costs nothing extra.** A measure evaluates on *any* set, so the
   descent works verbatim over all stagewise subsets.
2. **B's boundedness needs `[∀ i, IsProbabilityMeasure (μ i)]`**, an assumption that
   then propagates through every later statement, where A gets the bound from the
   already-established `normalizedCounting_le_one`.
3. **B's additivity is the real problem, and the spike does not reach it.** Finite
   additivity of the content requires the *stagewise* sets to be measurable, which
   `InternalSet` does not record. Under B, either `InternalSet` must change — the
   refactor the Layer I caveat exists to prevent — or a separate
   `InternalMeasurableSet` must arrive before the content can be additive at all.

So the general API is not "no harder": it is harder at exactly the point where the
construction stops being a definition and starts being a measure.

## Decision

**Counting-first.**

- M3 constructs the internal content for **finite discrete stages**, using
  `Loeb.normalizedCounting`.
- `InternalSet` continues to contain **all** stagewise subsets, unchanged.
- General measured families arrive later as an *addition*: a separate
  `InternalMeasurableSet` with a forgetful map, and a measure-parameterized content.
  They do **not** refactor the basic internal-set layer.
- C2 introduces **no** stage-measure parameter and **no** generic all-set evaluator.

## Consequences

- The content's signature is `internalContent (U) (A : InternalSet U X) : ℝ≥0∞`, with
  finiteness and discreteness as instance hypotheses on the stages rather than a
  measure argument.
- Elek–Szegedy is reachable with no further generalization; Hoover's varying
  probability spaces will need the `InternalMeasurableSet` layer, which is additive
  work rather than a rewrite.
- The Layer I caveat is upheld: the generalization cost stays in the content's domain.
- Should the later general layer prove awkward, the fallback is to parameterize the
  content and prove the counting case is its instance — which the spike shows is a
  signature change, not a re-proof.
