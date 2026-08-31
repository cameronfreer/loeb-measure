## Outcome

What mathematical or API capability does this PR add?

Closes #

## Design and assumptions

- Applicable ADR:
- Explicit finiteness/nonempty/ultrafilter/freeness/measurability assumptions:
- Upstream candidate or Loeb-specific:

## Verification

- [ ] `lake build`
- [ ] No `sorry` in scope
- [ ] No new nonstandard axioms
- [ ] If a public module or capability changed, consider naming new entry points in `scripts/AxiomAudit.lean` (documentation only — coverage is automatic)
- [ ] If this PR implements blueprint sketches, they are replaced by a pointer to the compiled module
- [ ] Public declarations and modules have docstrings
- [ ] Examples use the public API rather than quotient unfolding
- [ ] Roadmap/blueprint/decision records updated if assumptions or dependencies changed

## Reviewer notes

Call out delicate quotient, completion, measurable-space, or finite-power equivalence
choices here.
