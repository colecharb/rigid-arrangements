# Rigid Arrangements: project guide

A math research project: enumerating "rigid" arrangements of tangent unit circles
in the plane, up to isomorphism, for `n` circles. The full problem statement lives in
`docs/problem.md`. Treat it as authoritative, and record any interpretation choices there.

## Ground rules

- **Everything is done in Lean 4 + Mathlib.** Definitions, theorems, and the
  enumeration itself (computable Lean code, or `decide`/`native_decide` proofs where
  it helps). Don't fall back to Python or other languages for the math.
- **Explain in English at regular intervals.** After each meaningful milestone
  (a new definition, a proved theorem, an enumeration result), add a dated entry to
  `docs/journal.md`. Say what was done, what it means mathematically, and what
  comes next. Write for a mathematician who doesn't read Lean.
- Never leave `sorry` in committed code without a note in the journal saying so.
- Be careful with the hexomino analogy: the user suspects the match with
  hexominoes is *not* exact. Look for where it breaks down instead of assuming it.

## Tooling

- Lean toolchain is managed by elan (`~/.elan/bin`). The version is pinned in
  `lean-toolchain` and matches the Mathlib release in `lakefile.toml`.
- Build: `lake build`. After bumping Mathlib, run `lake exe cache get` first.
- Lean source lives under `RigidArrangements/`. Import every new file from
  `RigidArrangements.lean`.

## Commits

Atomic commits in Conventional Commits format, e.g. `feat(rigidity): define
infinitesimal rigidity`, `docs(journal): summarize n ≤ 4 enumeration`.
