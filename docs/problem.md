# Problem statement

> **Status:** informal statement received. Making it rigorous is the current task.

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

## Known requirements

1. Circles are unit circles in the plane, and no two overlap.
2. Each circle touches tangentially (at least?) two others.
3. **Rigidity:** if every existing tangency is kept, the arrangement has no "wiggle
   room" (no continuous deformation).
4. **Check:** two circles are not rigid, and the only rigid arrangement of 3 circles
   is the equilateral triangle.

## Open questions (to be settled by the research phase or by the user)

1. Does "touch two other circles" mean *at least* two? Reading it as *exactly* two
   allows only cycles, so the triangle would be the only rigid arrangement.
2. Which rigidity notion fits: no continuous motion, an isolated point up to
   congruence, or infinitesimal rigidity? These can differ in degenerate cases.
3. In standard rigidity theory, two circles "rolling" around each other is a rigid
   motion of the pair, not a deformation. So what excludes two circles: the "touches
   two others" clause, or something else?
4. What does *isomorphism* mean: congruence (with or without reflections) after
   relabeling, or isomorphism of the contact graph?
5. Does the arrangement have to be connected? (Rigidity probably forces it.)
6. "Hexominoes" normally means 6-square polyominoes. Circles placed on the
   triangular lattice correspond to **polyhexes**. Which one is meant, and where does
   the correspondence break?
