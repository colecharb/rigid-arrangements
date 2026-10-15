# Exploratory computations

Everything in this folder is **exploratory**: plain Lean programs (no theorems, not imported by
`RigidArrangements.lean`, not built by CI). Their outputs are recorded as *[computed]* in
`docs/formula-plan.md` and `docs/journal.md`, never as proved. Proved results live in
`RigidArrangements/`.

| file | what it is |
|---|---|
| `RigidEnum.lean` | Census of rigid arrangements on the triangular lattice: Henneberg extension of all rigid sets of size n − 1 plus a pruned search for rigid cores, exact rank of the rigidity matrix, canonical forms under the 12 lattice symmetries. Modes `polyhex N`, `hash N`, `orderly N`, `controls N`, `decide25`. |
| `orderly25.txt` | Output of `RigidEnum orderly 25`: per-n counts (rigid, cores, singular, saturated polyiamond corner sets, …) for n = 3..25. |
| `decide25.txt` | The four n = 25 candidates that needed higher-order analysis, and their verdicts. |
| `JudgeEnum.lean`, `judge19.txt` | The judge's re-run to n = 19: fixed counts, profile-key collisions, max-contact counts. |
| `NonSaturated26.lean` | The 26-circle polyiamond corner set whose spanned triangles are not edge-connected. |
| `Glue.lean` | Prototype of the gluing (concatenation) argument behind the growth-constant plan (WS1). |

## Running

Small cases run in the interpreter, e.g. `lake env lean explore/RigidEnum.lean` (ends with
`#eval main ["orderly", "13"]`). The large cases were run as a compiled binary:

```bash
lake env lean -c RigidEnum.c explore/RigidEnum.lean
leanc -O3 RigidEnum.c -o RigidEnum      # leanc from the same toolchain
./RigidEnum orderly 25
```

The n = 25 run took about 16 minutes for the core search on this machine. The counts for
n ≥ 16 rest on one pruned core-search code lineage; see the caveats in `docs/formula-plan.md`.
