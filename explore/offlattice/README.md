# Off-lattice exploration

Exploratory Lean behind `docs/offlattice.md`. Nothing here is imported by the library or built
by CI; results are recorded there as *[computed-exact]*, *[computed-float]* or *[Lean-scratch]*.

| path | what it is |
|---|---|
| `proto/OffLatticeProto.lean` | **Kernel-checked** prototypes against the library (`import RigidArrangements`; standard axioms only, no `sorry`): the frame criterion `isLattice_iff_frameInv` / `IsRigid.not_isLattice_iff`, the body lemma `isLattice_of_triGrown`, the reduction `isLattice_of_card_le_ten_of_cores`, and the certified off-lattice examples `ex13`, `ex15`, `ex17` (rigid, not on the lattice). Candidates for promotion into `RigidArrangements/`. Check with `lake env lean explore/offlattice/proto/OffLatticeProto.lean` (about a minute). The other files in `proto/` are the pieces it was assembled from. |
| `catalogue/` | Exact catalogue of off-lattice cores and their Henneberg closures (`MainAll`, `MainVerify`, …), the bond-breaking landscape search, and their outputs (`out*.txt`). `build.sh` compiles the drivers. |
| `structure/` | Enumerators for the structure theory: two-body hinge + bar (`TwoBody`), three-body rings (`Rings`), fans (`Fan`). |
| `adversary/` | The counterexamples to the strong hypothesis: `H30CertI.lean` (free braced rhombus, interval certificate) and `ChainExact.lean` (E30, taut chain). |
| `Figs.lean` | Floating-point recheck of the figure coordinates (contacts, overlaps, rank, direction classes). |
