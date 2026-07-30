# Loeb Measure in Lean

Loeb measure, ultraproduct probability, and applications to exchangeability and graph
limits, in Lean 4 / [mathlib](https://github.com/leanprover-community/mathlib4).

The repository is currently a scaffold: the build, the root import spine, and CI are
wired up, but the mathematical content has not landed yet.

## Building

The project pins Lean `v4.32.2` and the mathlib revision at that tag
(`905b95818eb32af7874a58b427f50c1711a5e96c`), so it builds against exactly one mathlib.

```bash
lake exe cache get   # mathlib build cache
lake build
```

## Layout

```
LoebMeasure.lean       root import spine
LoebMeasure/Basic.lean placeholder module
```

Declarations live principally in the `Loeb` namespace:

```lean
import LoebMeasure

open Loeb
```

## License

Apache-2.0. See [LICENSE](LICENSE).
