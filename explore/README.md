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
| `Constructible.lean` | `RigidEnum.lean` plus the R1–R4 cluster-merging calculus: clusters as bitmasks seeded with the contact atoms, kept R1-saturated, driven to a fixpoint by R1 (share ≥ 2 circles), R2 (distinct representatives), R3 (taut straight chain) and R4 (three bars of independent lines). Reports `constructible=`/`emergent=` per n and prints every emergent class. Modes `orderly N [verifyUpTo]` (full census; `verifyUpTo` is the largest n at which the fixpoint is also run on *every* rigid set, to check that constructibility is inherited along Henneberg steps), `cores N` (core candidates only, which is complete for "smallest emergent"), `landmarks`, `selftest`. |
| `constructible22.txt` | Output of `Constructible orderly 22 22`: the headline census. Rigid lattice arrangements for n = 1..22 split into constructible and emergent under R1+R2, R1+R2+R4 and full R1–R4; `emergent R1234` is 0 for every n ≤ 19, then 1, 12, 99 at n = 20, 21, 22. The unique smallest emergent arrangement is **S20** (`lmS20`), whose R1–R4 fixpoint stalls at five clusters of sizes {16, 4, 2, 2, 2}; its three cross bars lie on the lattice lines b = 4, a + b = 4 and a = 0, which are concurrent at (0, 4), so their 3 × 3 line determinant vanishes and R4 cannot fire. `verifyAll=true` at every n (hence the second `22`), and `inheritanceViolations=0` throughout. |
| `constructible-cores22.txt` | Output of `Constructible cores 22`: the same calculus run on core candidates only, deciding rigidity from scratch (cheap flex certificates, then exact rank, Asimow–Roth, the parallel flex, "some deletion is rigid", second order) instead of from the previous census level. This is the mode that carries the **soundness cross-check**: a candidate with a flex certificate that the calculus nevertheless merges would print `SOUNDNESS VIOLATION` and be counted in `soundnessViolations`. That count is **0 at every n = 3..22**. Its rigid-core counts (128, 236, 501 at n = 20, 21, 22) agree with `rigidCores=` in `constructible22.txt`, and its emergent cores are 0 for n ≤ 19, then 1, 6, 7 — the n = 20 one being S20 again. |
| `NonSaturated26.lean` | The 26-circle polyiamond corner set whose spanned triangles are not edge-connected. |
| `Glue.lean` | Prototype of the gluing (concatenation) argument behind the growth-constant plan (WS1). |
| `caseb/` | The case-(b) minimality search: is there an off-lattice arrangement smaller than H30 whose off-lattice information is carried by circles lying in no triangle? There is not, and both known mechanisms are exactly minimal at n = 30. Has its own `README.md` and `build.sh`. |
| `gf/` | Strips of bounded width: brute force, line-sum transfer matrices, generating functions and growth constants for widths 3 to 6, and the width at which emergence begins. Has its own `README.md`. |
| `offlattice/` | The off-lattice investigations; self-documenting, see `offlattice/README.md`. |

## Running

None of these files is imported by `RigidArrangements.lean`, so **do not** reach for `lake build`.
Each is a standalone program over `Std` only (no Mathlib), so it elaborates in seconds.

`RigidEnum.lean` ends with `#eval main ["orderly", "13"]`, so small cases run in the interpreter
with `lake env lean explore/RigidEnum.lean`. `Constructible.lean` has **no** `#eval`; drive it
through `main` instead, e.g. `lake env lean --run explore/Constructible.lean selftest`.

The large cases were run as a compiled binary:

```bash
lake env lean  -c RigidEnum.c explore/RigidEnum.lean
lake env leanc -O3 RigidEnum.c -o RigidEnum     # leanc from the same toolchain
./RigidEnum orderly 25
```

The n = 25 run took about 16 minutes for the core search on this machine. The counts for
n ≥ 16 rest on one pruned core-search code lineage; see the caveats in `docs/formula-plan.md`.

### The invocations that produce the `Constructible` outputs

```bash
lake env lean  -c Constructible.c explore/Constructible.lean   # ~3 s
lake env leanc -O3 Constructible.c -o Constructible            # ~7 s
./Constructible orderly 22 22 > explore/constructible22.txt        # ~83 s
./Constructible cores 22      > explore/constructible-cores22.txt  # ~12 s
```

Both outputs have been reproduced from `explore/Constructible.lean` as it stands here, by exactly
these commands (2026-10-27). `orderly 22 22` came back **byte-identical to `constructible22.txt`
apart from the 20 `time ms:` lines**: 6 of those matched anyway and 14 differ, the re-run
totalling 83.1 s of reported compute against the earlier run's 101.6 s. The other 378 lines —
every count, every
`verifyAll`/`inheritanceViolations` flag and every emergent class — match exactly. The two
arguments matter: the second `22` is `verifyUpTo`, and dropping it defaults to 16, which would
leave `verifyAll=false` for n ≥ 17.

Compiling the file is not the bottleneck anyone might fear from its 2300 lines: it imports only
`Std.Data.HashMap`/`HashSet`, so `lean -c` takes ~3 s and `leanc -O3` ~7 s.

`cores 22` is the run to repeat when the question is soundness rather than counts: grep its
output for `soundnessViolations` (0 at every level) and for `SOUNDNESS VIOLATION` (no
occurrences). `constructibleMode` has no such check, because it only ever classifies sets that
the previous census level has already decided rigid; its `inheritanceViolations` counter is a
different thing (monotonicity of constructibility along Henneberg steps).

`./Constructible selftest` is the cheapest check that the rule semantics are the intended ones —
in particular that R2 refuses three atoms through one circle, that R3 refuses a free straight
chain, and that R4 refuses S20's three concurrent bars (it also recomputes S20's unpruned closure,
145 clusters). It runs in the interpreter and prints the same six lines there as compiled.
