# Contributing

The project is proof-oriented and dependency-sensitive. Small, compiling seams are
more useful than broad PRs containing many provisional definitions.

## Before starting

1. Pick an issue from the current milestone.
2. Check its blocking issues and declaration sketch in
   [docs/blueprint.md](docs/blueprint.md).
3. For a foundational API choice, complete or update the relevant decision record
   before writing downstream modules.
4. Comment on the issue with the declarations you intend to add or change.

Research questions use the research issue form. Proof/API work uses the implementation
issue form.

## Building

```bash
lake exe cache get
lake build
```

The package pins Lean and mathlib. Do not update either pin as part of an unrelated
mathematical change.

## Lean style

- Follow mathlib naming, documentation, and import conventions.
- Keep `autoImplicit = false` compatibility.
- Declarations specific to this library live under `Loeb`; generic additions use the
  natural mathlib namespace such as `Filter.Product`.
- Use `Fin n → Ω` for finite powers.
- Add simp lemmas for representative constructors, coordinate maps, and equivalences.
- Keep quotient induction inside the lowest possible module.
- Do not add axioms or weaken a theorem statement to finish a proof.
- Do not use the root `import LoebMeasure` inside library modules.

Every public declaration needs a docstring. Every module needs a module docstring that
states its mathematical purpose and principal declarations.

## Pull-request size

A good foundational PR usually adds one of:

- one data type plus its elementary API;
- one equivalence plus its naturality/simp lemmas;
- one mathematical lemma and the local helpers needed by its proof; or
- one research spike whose result is a decision record and a compiling scratch test
  promoted into the library where appropriate.

Avoid combining unrelated cleanup, dependency updates, and mathematical work.

## Scratch work and design branches

`main` is strict: `warningAsError` is on and `sorry` is a warning, so exploratory
skeletons do not compile there and must not land there. Test candidate signatures in
scratch files or on a design branch; land proven definitions and theorems
incrementally. Future theorem statements belong in
[docs/blueprint.md](docs/blueprint.md) and issues, not in `sorry` stubs on `main`.

## Definition of done

Before requesting review:

```bash
lake build
```

and confirm:

- no `sorry` in the PR scope;
- no new nonstandard axioms;
- no linter warnings (warnings are errors in this package);
- public declarations have docstrings;
- tests/examples use the public API rather than unfolding quotients;
- the root import is updated only for a completed public module;
- issue acceptance criteria are checked off; and
- roadmap, blueprint, or decision documents are updated if assumptions changed.

For a theorem intended for upstreaming, also minimize imports and note the proposed
mathlib module and namespace in the PR.

## Proof review

Reviews check three levels:

1. **Mathematics:** the theorem has the intended assumptions, especially around
   nonempty fibers, freeness, completion, and graded measurable spaces.
2. **API:** downstream users do not need representative or quotient manipulation.
3. **Engineering:** the import graph remains acyclic and the declaration belongs in
   the stated layer.

The strongest warning sign is a proof of graded Fubini that silently replaces the
degree-`m+n` Loeb measurable space with an ordinary product measurable space.

## Commits and issue references

Use descriptive commit subjects. Reference the issue in the PR body, and use
`Closes #…` only when every acceptance criterion is met. Research issues close when
their decision record is accepted, not merely when an experiment was attempted.
