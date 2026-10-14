# Problem statement

> **Status:** definitions settled (2026-10-14). The Lean definitions in
> `RigidArrangements/Basic.lean` and `RigidArrangements/Rigidity.lean` are authoritative;
> this page explains them and records every interpretation choice.

## The user's statement (verbatim)

> We define a rigid arrangement as a set of unit circles in the plane that each
> touch tangentially to two other circles and no two circles overlap. We also want
> the arrangement to be such that, if the circles were all attracted to one another
> (like magnets), there would be no "wiggle room" while keeping everything touching
> tangentially as it is. For example, two circles cannot be rigid since they can only
> touch tangentially in one location, and would be able to "roll" around one another
> while staying tangent.

> The only rigid arrangement for three circles is where their centers lie on the
> vertices of an equilateral triangle.

Further context from earlier:

- Rigid arrangements are "almost 1:1 with hexominoes, but I don't think they quite are."
- **Goal:** enumerate rigid arrangements of `n` circles **up to isomorphism**.

## Formal definitions

The user asked for definitions from an existing field rather than custom ones. We use
**rigidity theory of bar frameworks**.

- **Arrangement.** Finitely many unit circles in the plane, given by their centers, with no
  two overlapping (distinct centers at distance ≥ 2). Lean: `Arrangement ι`, with the plane
  modeled as `ℂ`.
- **Contact graph.** One vertex per circle, and an edge for each tangent pair (centers
  exactly 2 apart). Lean: `Arrangement.contactGraph`.
- **Rigid.** The arrangement is *locally rigid* as a bar framework, with one bar of
  length 2 for each tangent pair. Some ε > 0 has this property: every placement that moves
  each center by less than ε and keeps every tangency has the same pairwise distances as
  the original. New tangencies may form. This is the standard definition (Asimow–Roth
  1978; Jackson's *Notes on the rigidity of graphs*). By the Asimow–Roth theorem it is
  equivalent to "no continuous motion that keeps the tangencies changes the shape", which
  is the user's "no wiggle room". Lean: `Arrangement.IsRigid`, `IsLocallyRigid`.
- **Isomorphic.** Some relabeling of the circles makes all pairwise distances agree.
  Equivalently, one arrangement is carried to the other by a relabeling and an isometry
  of the plane, **reflections allowed**. Lean: `Arrangement.Iso`; the objects counted are
  `RigidClasses n`.

## Interpretation decisions

1. **"Touches two other circles" is not part of the definition.** (User's decision,
   2026-10-14: prefer the standard definition.)
   - For n ≥ 3, rigidity already forces every circle to touch at least two others. A
     circle touching at most one other could be rotated around it.
   - In the standard theory, one circle is rigid, and so are two tangent circles. Rolling
     one around the other moves the pair as a whole without changing its shape. So with
     this definition the counts for n = 1 and n = 2 are 1 each (trivially). The
     enumeration of interest starts at n = 3.
   - Reading the clause as *exactly* two would make the contact graph a union of cycles.
     A ring of 4 or more equal circles always flexes, so only the triangle would ever be
     rigid. That reading is not the intended one.
2. **Rigidity notion: local (nonlinear) rigidity, not infinitesimal rigidity.**
   - Infinitesimal rigidity (the rigidity matrix has rank 2n − 3) implies local rigidity.
     We use it only as a certificate.
   - Some arrangements are rigid but not infinitesimally rigid ("singular" ones): a circle
     squeezed exactly between two circles 4 apart. These count as rigid, as in the standard
     theory. The research phase found that none exist with fewer than 18 circles on the
     triangular lattice (exploratory computation, not yet a theorem).
3. **Mirror images count as the same arrangement** (user's decision, 2026-10-14). Free
   counts, as in "35 hexominoes". One-sided counts first differ at n = 6, where the
   parallelogram of 6 circles is chiral.
4. **Connectedness is not imposed.** Rigidity forces it for n ≥ 2.
5. **Arrangements off the triangular lattice count.** Nothing in the statement restricts
   to a grid. The first known one has 11 circles (see `docs/journal.md`).

## Still open

- **What "hexominoes" meant.** The evidence points to *polyiamonds*, shapes made of
  triangles, specifically the 12 hexiamonds. See the journal entry of 2026-10-14 for the
  detailed comparison. Square hexominoes can never be rigid. Awaiting the user's
  confirmation.
- **Trust in large computations.** Is `native_decide`, which trusts the Lean compiler, acceptable
  for large certified enumerations? Until the user decides, only kernel-checked `decide`
  is used.
