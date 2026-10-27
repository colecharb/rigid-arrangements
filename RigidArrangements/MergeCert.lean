import RigidArrangements.Cluster
import RigidArrangements.Cores78

/-!
# Merge certificates: a decidable checker for the cluster calculus

`RigidArrangements.Cluster` turns "these circles do not move relative to one another" into the
predicate `Arrangement.RigidIn` and proves the three merging rules R1, R2, R3. This file makes
the bookkeeping of a *chain of merges* into data that the Lean kernel can check.

## The idea

A rigidity proof in the calculus is a short script: start from a list of contacts, each of which
is a cluster of two circles (`Arrangement.rigidIn_pair`); then repeatedly merge clusters by one of
the rules, each merge producing a new cluster; stop when one cluster contains every circle, and
cash that in by `Arrangement.rigidIn_univ_iff`. Nothing in the script needs to know where the
circles are. Which clusters a rule consumes, which circles they share, which contacts form a
chain — all of that is combinatorics, and all of it is decidable.

So a *certificate* (`MergeCert`) is a list of contacts together with a list of steps
(`MergeStep`), each step naming the clusters it consumes by their position in the list of clusters
built so far (the contacts seed positions `0, 1, …`, and each step appends its result at the end).
The checker `checkMerge` replays the script and returns a `Bool`.

## What the checker cannot see

The checker never looks at a center, so the caller must supply the geometry. Exactly two kinds of
fact are needed, and no others:

* **every listed contact really is a contact**, `∀ e ∈ cert.edges, Tangent A.center e.1 e.2`.
  This list need only be *sound*, not complete: a certificate may use fewer contacts than the
  arrangement has, and extra contacts of the arrangement are simply never mentioned.
* **for each R3 step, one distance**, `dist (A.center u) (A.center v) = 2 * k`, where `u` and `v`
  are the ends of the chain and `k` its number of contacts. `mergeAnchors` collects these
  demands from the step list, so there is one hypothesis covering all of them. R1 and R2 steps
  demand nothing: as the docstrings of `Arrangement.RigidIn.union_of_two` and
  `Arrangement.RigidIn.union_of_ring` explain, those rules have no non-degeneracy condition.

## Circles and their names

The soundness theorem `Arrangement.isRigid_of_checkMerge` is stated with a *naming* map
`name : ι → κ`, injective, from the circles of the arrangement to whatever the certificate calls
them. The point of the extra generality is the lattice layer below, where it is natural to write a
certificate in terms of lattice points while the arrangement is indexed by positions in a list.
For a certificate written in terms of the circles themselves take `name = id`, which is
`Arrangement.isRigid_of_checkMerge_self`.

`name` is not assumed surjective: a name the certificate uses need not be a circle at all. Such a
name can never enter a cluster, because every name in a cluster arrives as an endpoint of a listed
contact, and the caller's contact hypothesis produces a circle for it. This is tracked by
`Arrangement.IsClusterList`, the invariant the replay maintains: *each name in the cluster is the
name of a circle, and the circles so named form a cluster of `A`*.

## The lattice layer

On the triangular lattice every side condition becomes integer arithmetic, so no geometry has to
be supplied at all: a contact between lattice points `v`, `w` is `eNorm (v - w) = 1`
(`tangent_latticePoint_iff`) and an R3 anchor distance `2 * k` is `eNorm (v - w) = k ^ 2`
(`dist_latticePoint_sq`, and `dist_latticePoint_eq_two_mul` below). So `checkMergeL` folds the
two caller obligations into arithmetic checks, and
`Arrangement.isRigid_ofLattice_of_checkMergeL` has no geometric hypothesis: every instance closes
by `decide +kernel`.

## Instances

* `Arrangement.o11_isRigid_of_mergeCert`: the off-lattice arrangement `O11`, by a layer-one
  certificate of nine R2 steps over the nineteen contacts. Compare
  `Arrangement.o11_isRigid_of_cluster`, which assembles the same proof by hand from two rigid
  chevrons and the bar; the certificate instead builds each chevron from its contacts, since R2
  subsumes a Henneberg step.
* `Arrangement.flower_isRigid_of_mergeCert` and
  `Arrangement.flower_isRigid_of_mergeCert_chain`: the flower (`Arrangement.flower`), by a
  lattice certificate, twice. The second certificate is the first with one R3 step added; see its
  docstring for why the step is redundant and included anyway.

## Adding R4

R4 is not part of the calculus yet. When it arrives it is a one-constructor change: add a
constructor to `MergeStep`, a branch to `MergeStep.run` (its combinatorial side conditions) and to
`MergeStep.anchors` (the geometric facts it needs of the caller, if any), and a case to
`Arrangement.isClusterList_run`. Nothing else in this file mentions the individual rules.

## Main results

* `MergeStep`, `MergeCert`, `MergeStep.run`, `mergeFrom`, `mergeClusters`, `checkMerge`: the
  checker.
* `Arrangement.IsClusterList`, `Arrangement.isClusterList_mergeClusters`: the invariant and its
  propagation.
* `Arrangement.isRigid_of_checkMerge`, `Arrangement.isRigid_of_checkMerge_self`: soundness.
* `checkMergeL`, `Arrangement.isRigid_ofLattice_of_checkMergeL`: the lattice layer.
* `o11MergeCert`, `Arrangement.o11_isRigid_of_mergeCert`, `flowerMergeCert`,
  `Arrangement.flower_isRigid_of_mergeCert`, `flowerChainMergeCert`,
  `Arrangement.flower_isRigid_of_mergeCert_chain`.
-/

namespace RigidArrangements

/-! ## Certificates -/

/-- One step of the merging calculus. The clusters a step consumes are named by their position in
the list of clusters built so far: the listed contacts seed positions `0, 1, …` in order, and each
step appends the cluster it produces at the end. An out-of-range position is read as the empty
cluster, which makes every step that mentions it fail. -/
inductive MergeStep (κ : Type*) where
  /-- **R1**: merge the clusters at positions `s` and `t`, which share the two distinct circles
  `a` and `b`. -/
  | r1 (s t : ℕ) (a b : κ) : MergeStep κ
  /-- **R2**: merge the clusters at positions `s`, `t`, `u`, which pairwise share the distinct
  circles `z` (in the first two), `x` (in the last two) and `y` (in the first and the last). -/
  | r2 (s t u : ℕ) (x y z : κ) : MergeStep κ
  /-- **R3**: merge into the cluster at position `s` the taut chain `u :: rest`, whose ends `u`
  and `rest.getLastD u` lie in that cluster and whose consecutive pairs are listed contacts. -/
  | r3 (s : ℕ) (u : κ) (rest : List κ) : MergeStep κ
  deriving Repr

/-- A **merge certificate**: the contacts to start from, and the merging steps to apply in
order. -/
structure MergeCert (κ : Type*) where
  /-- The contacts the certificate uses. Each one seeds a cluster of two circles, in this order,
  and each one must really be a contact of the arrangement. -/
  edges : List (κ × κ)
  /-- The merging steps, applied in order. -/
  steps : List (MergeStep κ)
  deriving Repr

namespace MergeStep

variable {κ : Type*}

/-- The geometric demands of a step: a list of triples `(u, v, k)`, each asking that the circles
named `u` and `v` be at distance exactly `2 * k`. R1 and R2 demand nothing; an R3 step demands the
one distance that makes its chain taut. -/
def anchors : MergeStep κ → List (κ × κ × ℕ)
  | r1 _ _ _ _ => []
  | r2 _ _ _ _ _ _ => []
  | r3 _ u rest => [(u, rest.getLastD u, rest.length)]

end MergeStep

/-- The geometric demands of a whole step list, gathered in one place so that a single hypothesis
covers them all. -/
def mergeAnchors {κ : Type*} (steps : List (MergeStep κ)) : List (κ × κ × ℕ) :=
  steps.flatMap MergeStep.anchors

/-- The clusters a certificate starts from: one two-circle cluster per listed contact, in the
order the contacts are listed. -/
def mergeAtoms {κ : Type*} (E : List (κ × κ)) : List (List κ) :=
  E.map fun e => [e.1, e.2]

section Checker

variable {κ : Type*} [DecidableEq κ]

/-- The unordered pair `{x, y}` occurs in the contact list `E`. -/
def isEdge (E : List (κ × κ)) (x y : κ) : Bool :=
  E.any fun e => decide (e = (x, y)) || decide (e = (y, x))

/-- Every consecutive pair of the chain `x :: ys` occurs in the contact list `E`. -/
def chainEdges (E : List (κ × κ)) : κ → List κ → Bool
  | _, [] => true
  | x, y :: t => isEdge E x y && chainEdges E y t

/-- Run one step against the clusters built so far, returning the new cluster, or `none` if a
side condition fails. Positions are read with `List.getD _ []`, so an out-of-range position
behaves like an empty cluster and the step fails. -/
def MergeStep.run (E : List (κ × κ)) (cs : List (List κ)) : MergeStep κ → Option (List κ)
  | .r1 s t a b =>
      if a ∈ cs.getD s [] ∧ a ∈ cs.getD t [] ∧ b ∈ cs.getD s [] ∧ b ∈ cs.getD t [] ∧ a ≠ b then
        some (cs.getD s [] ++ cs.getD t [])
      else none
  | .r2 s t u x y z =>
      if z ∈ cs.getD s [] ∧ z ∈ cs.getD t [] ∧ x ∈ cs.getD t [] ∧ x ∈ cs.getD u [] ∧
          y ∈ cs.getD s [] ∧ y ∈ cs.getD u [] ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z then
        some (cs.getD s [] ++ cs.getD t [] ++ cs.getD u [])
      else none
  | .r3 s u rest =>
      if rest ≠ [] ∧ u ∈ cs.getD s [] ∧ rest.getLastD u ∈ cs.getD s [] ∧
          chainEdges E u rest = true then
        some (cs.getD s [] ++ u :: rest)
      else none

/-- Replay a list of steps against a list of clusters, appending each new cluster at the end. -/
def mergeFrom (E : List (κ × κ)) (cs : List (List κ)) :
    List (MergeStep κ) → Option (List (List κ))
  | [] => some cs
  | s :: rest => (s.run E cs).bind fun c => mergeFrom E (cs ++ [c]) rest

/-- All the clusters a certificate builds: the atoms of its contacts, then one more for each
step. -/
def mergeClusters (cert : MergeCert κ) : Option (List (List κ)) :=
  mergeFrom cert.edges (mergeAtoms cert.edges) cert.steps

/-- **The checker.** `checkMerge cert all` replays the certificate and asks that the cluster
produced by the last step contain every name in `all`. With `all` a list of names covering every
circle, this says that the last cluster is the whole arrangement. -/
def checkMerge (cert : MergeCert κ) (all : List κ) : Bool :=
  match mergeClusters cert with
  | none => false
  | some cs =>
      match cs.getLast? with
      | none => false
      | some cl => all.all fun x => decide (x ∈ cl)

end Checker

/-! ## Two list facts -/

/-- The last entry of `a :: l`, read by its index, is `l.getLastD a`. -/
private theorem getD_length_cons {α : Type*} (a : α) (l : List α) (d : α) :
    (a :: l).getD l.length d = l.getLastD a := by
  induction l generalizing a d with
  | nil => rfl
  | cons b t ih =>
      rw [List.getLastD_cons, ← ih b d]
      simp

/-- The entries of `a :: l`, read by the indices `0, …, l.length`, are exactly its members. -/
private theorem image_getD_Iic {α : Type*} (a : α) (l : List α) :
    (fun m => (a :: l).getD m a) '' Set.Iic l.length = {x | x ∈ a :: l} := by
  ext x
  simp only [Set.mem_image, Set.mem_Iic, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hlt : m < (a :: l).length := by simp only [List.length_cons]; omega
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  · intro hx
    obtain ⟨m, hm, he⟩ := List.getElem_of_mem hx
    refine ⟨m, ?_, ?_⟩
    · simp only [List.length_cons] at hm; omega
    · rw [List.getD_eq_getElem _ _ hm]; exact he

namespace Arrangement

/-! ## The invariant -/

variable {ι κ : Type*} {A : Arrangement ι} {name : ι → κ}

/-- The circles of `A` whose names occur in the list `c`. -/
def namedSet (name : ι → κ) (c : List κ) : Set ι :=
  {i | name i ∈ c}

/-- Membership in `namedSet` is membership of the name in the list. -/
theorem mem_namedSet {c : List κ} {i : ι} (h : name i ∈ c) : i ∈ namedSet name c :=
  h

/-- The names of a concatenation name the union. -/
theorem namedSet_append (name : ι → κ) (c d : List κ) :
    namedSet name (c ++ d) = namedSet name c ∪ namedSet name d := by
  ext i
  simp only [namedSet, Set.mem_ofPred_eq, List.mem_append, Set.mem_union]

/-- If `name` is injective, the circles named by `qs.map name` are exactly the members of
`qs`. -/
theorem namedSet_map (hinj : Function.Injective name) (qs : List ι) :
    namedSet name (qs.map name) = {i | i ∈ qs} := by
  ext i
  simp only [namedSet, Set.mem_ofPred_eq, List.mem_map]
  exact ⟨fun ⟨j, hj, he⟩ => hinj he ▸ hj, fun hi => ⟨i, hi, rfl⟩⟩

/-- **The invariant the replay maintains.** Every name in `c` is the name of a circle, and the
circles so named form a cluster of `A`. The first half is what lets a rule turn a shared *name*
into a shared *circle*; it is why `name` need not be surjective. -/
def IsClusterList (A : Arrangement ι) (name : ι → κ) (c : List κ) : Prop :=
  (∀ x ∈ c, ∃ i, name i = x) ∧ A.RigidIn (namedSet name c)

/-- The empty cluster satisfies the invariant. This is what an out-of-range position reads as. -/
theorem isClusterList_nil : IsClusterList A name ([] : List κ) := by
  refine ⟨fun x hx => by simp at hx, ?_⟩
  have h : namedSet name ([] : List κ) = (∅ : Set ι) := by
    ext i; simp [namedSet]
  rw [h]
  exact rigidIn_of_subsingleton Set.subsingleton_empty

/-- **The atom of the calculus, under a naming.** Two tangent circles named `x` and `y` give a
cluster list `[x, y]`. -/
theorem isClusterList_pair (hinj : Function.Injective name) {x y : κ} {i j : ι}
    (hi : name i = x) (hj : name j = y) (ht : Tangent A.center i j) :
    IsClusterList A name [x, y] := by
  refine ⟨fun z hz => ?_, ?_⟩
  · rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨i, hi⟩
    · rcases List.mem_singleton.mp hz with rfl
      exact ⟨j, hj⟩
  · have h : namedSet name [x, y] = ({i, j} : Set ι) := by
      ext k
      simp only [namedSet, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (hk | hk)
        · exact Or.inl (hinj (hk.trans hi.symm))
        · exact Or.inr (hinj (hk.trans hj.symm))
      · rintro (rfl | rfl)
        · exact Or.inl hi
        · exact Or.inr hj
    rw [h]
    exact rigidIn_pair ht

/-! ## Reading the contact list -/

/-- A listed contact gives circles with the two names, tangent to each other. -/
theorem exists_tangent_of_isEdge [DecidableEq κ] {E : List (κ × κ)}
    (hE : ∀ e ∈ E, ∃ i j, name i = e.1 ∧ name j = e.2 ∧ Tangent A.center i j) {x y : κ}
    (h : isEdge E x y = true) : ∃ i j, name i = x ∧ name j = y ∧ Tangent A.center i j := by
  rw [isEdge, List.any_eq_true] at h
  obtain ⟨e, he, hxy⟩ := h
  obtain ⟨i, j, hi, hj, ht⟩ := hE e he
  rcases Bool.or_eq_true .. |>.mp hxy with h1 | h1
  · rw [decide_eq_true_eq] at h1
    subst h1
    exact ⟨i, j, hi, hj, ht⟩
  · rw [decide_eq_true_eq] at h1
    subst h1
    exact ⟨j, i, hj, hi, tangent_comm.mp ht⟩

/-- **A checked chain is a chain of contacts.** If the consecutive pairs of `ps` prefixed by the
name of `iu` are all listed contacts, there is a list `qs` of circles named by `ps` with
`iu :: qs` a chain of tangent circles. -/
theorem exists_chain_of_chainEdges [DecidableEq κ] (hinj : Function.Injective name)
    {E : List (κ × κ)}
    (hE : ∀ e ∈ E, ∃ i j, name i = e.1 ∧ name j = e.2 ∧ Tangent A.center i j) :
    ∀ (ps : List κ) (iu : ι), chainEdges E (name iu) ps = true →
      ∃ qs : List ι, qs.map name = ps ∧ List.IsChain (Tangent A.center) (iu :: qs) := by
  intro ps
  induction ps with
  | nil => exact fun iu _ => ⟨[], rfl, List.isChain_singleton _⟩
  | cons y t ih =>
      intro iu h
      simp only [chainEdges, Bool.and_eq_true] at h
      obtain ⟨i, j, hi, hj, ht⟩ := exists_tangent_of_isEdge hE h.1
      obtain rfl : i = iu := hinj hi
      obtain ⟨qs, hqs, hch⟩ := ih j (by rw [hj]; exact h.2)
      exact ⟨j :: qs, by rw [List.map_cons, hj, hqs],
        List.isChain_cons_cons.mpr ⟨ht, hch⟩⟩

/-! ## Soundness of one step -/

/-- **One step keeps the invariant.** Given the caller's contact hypothesis and the geometric
demands of this step, a step that succeeds against clusters satisfying the invariant produces a
cluster satisfying the invariant.

This is the only declaration in the file that mentions the individual rules: it applies
`Arrangement.RigidIn.union_of_two` for R1, `Arrangement.RigidIn.union_of_ring` for R2 and
`Arrangement.RigidIn.union_chain` for R3. -/
theorem isClusterList_run [Finite ι] [DecidableEq κ] (hinj : Function.Injective name)
    {E : List (κ × κ)}
    (hE : ∀ e ∈ E, ∃ i j, name i = e.1 ∧ name j = e.2 ∧ Tangent A.center i j)
    {cs : List (List κ)} (hcs : ∀ c ∈ cs, IsClusterList A name c) {s : MergeStep κ} {c : List κ}
    (hanch : ∀ t ∈ s.anchors, ∀ i j, name i = t.1 → name j = t.2.1 →
      dist (A.center i) (A.center j) = 2 * t.2.2)
    (h : s.run E cs = some c) : IsClusterList A name c := by
  -- the invariant also holds of the empty cluster an out-of-range position reads as
  have hcs' : ∀ n : ℕ, IsClusterList A name (cs.getD n []) := by
    intro n
    by_cases hn : n < cs.length
    · rw [List.getD_eq_getElem _ _ hn]
      exact hcs _ (List.getElem_mem hn)
    · have he : cs.getD n [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [he]
      exact isClusterList_nil
  cases s with
  | r1 sidx tidx a b =>
      simp only [MergeStep.run] at h
      split_ifs at h with hc
      obtain ⟨ha1, ha2, hb1, hb2, hab⟩ := hc
      rw [Option.some.injEq] at h
      subst h
      obtain ⟨ia, hia⟩ := (hcs' sidx).1 a ha1
      obtain ⟨ib, hib⟩ := (hcs' sidx).1 b hb1
      refine ⟨fun w hw => ?_, ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact (hcs' sidx).1 w hw
        · exact (hcs' tidx).1 w hw
      · rw [namedSet_append]
        exact (hcs' sidx).2.union_of_two (hcs' tidx).2
          (mem_namedSet (by rw [hia]; exact ha1)) (mem_namedSet (by rw [hia]; exact ha2))
          (mem_namedSet (by rw [hib]; exact hb1)) (mem_namedSet (by rw [hib]; exact hb2))
          fun he => hab (by rw [← hia, ← hib, he])
  | r2 sidx tidx uidx x y z =>
      simp only [MergeStep.run] at h
      split_ifs at h with hc
      obtain ⟨hz1, hz2, hx2, hx3, hy1, hy3, hxy, hxz, hyz⟩ := hc
      rw [Option.some.injEq] at h
      subst h
      obtain ⟨ix, hix⟩ := (hcs' tidx).1 x hx2
      obtain ⟨iy, hiy⟩ := (hcs' sidx).1 y hy1
      obtain ⟨iz, hiz⟩ := (hcs' sidx).1 z hz1
      refine ⟨fun w hw => ?_, ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · rcases List.mem_append.mp hw with hw | hw
          · exact (hcs' sidx).1 w hw
          · exact (hcs' tidx).1 w hw
        · exact (hcs' uidx).1 w hw
      · rw [namedSet_append, namedSet_append]
        exact (hcs' sidx).2.union_of_ring (hcs' tidx).2 (hcs' uidx).2
          (c₁ := ix) (c₂ := iy) (c₃ := iz)
          ⟨mem_namedSet (by rw [hiz]; exact hz1), mem_namedSet (by rw [hiz]; exact hz2)⟩
          ⟨mem_namedSet (by rw [hix]; exact hx2), mem_namedSet (by rw [hix]; exact hx3)⟩
          ⟨mem_namedSet (by rw [hiy]; exact hy1), mem_namedSet (by rw [hiy]; exact hy3)⟩
          (fun he => hxy (by rw [← hix, ← hiy, he]))
          (fun he => hxz (by rw [← hix, ← hiz, he]))
          (fun he => hyz (by rw [← hiy, ← hiz, he]))
  | r3 sidx u rest =>
      simp only [MergeStep.run] at h
      split_ifs at h with hc
      obtain ⟨hne, huS, hvS, hch⟩ := hc
      rw [Option.some.injEq] at h
      subst h
      obtain ⟨iu, hiu⟩ := (hcs' sidx).1 u huS
      obtain ⟨qs, hqs, hchain⟩ :=
        exists_chain_of_chainEdges hinj hE rest iu (by rw [hiu]; exact hch)
      -- the chain of circles, read off by index
      set w : ℕ → ι := fun m => (iu :: qs).getD m iu with hw
      have hlen : qs.length = rest.length := by
        rw [← hqs, List.length_map]
      have hk : 0 < qs.length := by
        rw [hlen]
        exact List.length_pos_iff.mpr hne
      have hmapcons : (iu :: qs).map name = u :: rest := by
        rw [List.map_cons, hiu, hqs]
      -- the far end of the chain
      have hwk : name (w qs.length) = rest.getLastD u := by
        have h1 : name (w qs.length) = ((iu :: qs).map name).getD qs.length (name iu) := by
          rw [hw, List.getD_map]
        rw [h1, hmapcons, hiu, hlen, getD_length_cons]
      have h0 : w 0 ∈ namedSet name (cs.getD sidx []) :=
        mem_namedSet (by rw [hw]; simpa using (by rw [hiu]; exact huS : name iu ∈ _))
      have hkS : w qs.length ∈ namedSet name (cs.getD sidx []) :=
        mem_namedSet (by rw [hwk]; exact hvS)
      have hstep : ∀ m < qs.length, Tangent A.center (w m) (w (m + 1)) := by
        intro m hm
        have h1 : m + 1 < (iu :: qs).length := by simp only [List.length_cons]; omega
        have h2 : m < (iu :: qs).length := by omega
        rw [hw]
        simp only
        rw [List.getD_eq_getElem _ _ h2, List.getD_eq_getElem _ _ h1]
        exact hchain.getElem m h1
      have hdist : dist (A.center (w 0)) (A.center (w qs.length)) = 2 * qs.length := by
        have ht : (u, rest.getLastD u, rest.length) ∈
            (MergeStep.r3 sidx u rest : MergeStep κ).anchors := by
          simp [MergeStep.anchors]
        have := hanch _ ht (w 0) (w qs.length) (by rw [hw]; simpa using hiu) hwk
        rw [this, hlen]
      have hres := (hcs' sidx).2.union_chain hk w h0 hkS hstep hdist
      refine ⟨fun v hv => ?_, ?_⟩
      · rcases List.mem_append.mp hv with hv | hv
        · exact (hcs' sidx).1 v hv
        · rw [← hmapcons, List.mem_map] at hv
          obtain ⟨j, _, hj⟩ := hv
          exact ⟨j, hj⟩
      · rw [namedSet_append]
        have himg : w '' Set.Iic qs.length = namedSet name (u :: rest) := by
          rw [← hmapcons, namedSet_map hinj, hw]
          exact image_getD_Iic iu qs
        rw [← himg]
        exact hres

/-! ## Soundness of the replay -/

/-- **The replay keeps the invariant.** -/
theorem isClusterList_mergeFrom [Finite ι] [DecidableEq κ] (hinj : Function.Injective name)
    {E : List (κ × κ)}
    (hE : ∀ e ∈ E, ∃ i j, name i = e.1 ∧ name j = e.2 ∧ Tangent A.center i j) :
    ∀ (steps : List (MergeStep κ)) (cs cs' : List (List κ)),
      (∀ c ∈ cs, IsClusterList A name c) →
      (∀ t ∈ mergeAnchors steps, ∀ i j, name i = t.1 → name j = t.2.1 →
        dist (A.center i) (A.center j) = 2 * t.2.2) →
      mergeFrom E cs steps = some cs' → ∀ c ∈ cs', IsClusterList A name c := by
  intro steps
  induction steps with
  | nil =>
      intro cs cs' hcs _ h
      rw [mergeFrom, Option.some.injEq] at h
      exact h ▸ hcs
  | cons s rest ih =>
      intro cs cs' hcs hanch h
      rw [mergeFrom, Option.bind_eq_some_iff] at h
      obtain ⟨c, hr, h⟩ := h
      have hsa : ∀ t ∈ s.anchors, ∀ i j, name i = t.1 → name j = t.2.1 →
          dist (A.center i) (A.center j) = 2 * t.2.2 := fun t ht =>
        hanch t (by rw [mergeAnchors, List.mem_flatMap]; exact ⟨s, List.mem_cons_self .., ht⟩)
      have hc : IsClusterList A name c := isClusterList_run hinj hE hcs hsa hr
      refine ih (cs ++ [c]) cs' (fun d hd => ?_) (fun t ht => ?_) h
      · rcases List.mem_append.mp hd with hd | hd
        · exact hcs d hd
        · rw [List.mem_singleton] at hd
          exact hd ▸ hc
      · exact hanch t (by
          rw [mergeAnchors, List.mem_flatMap] at ht ⊢
          obtain ⟨s', hs', ht'⟩ := ht
          exact ⟨s', List.mem_cons_of_mem _ hs', ht'⟩)

/-- **Every cluster a certificate builds is a cluster.** -/
theorem isClusterList_mergeClusters [Finite ι] [DecidableEq κ] (hinj : Function.Injective name)
    {cert : MergeCert κ} {cs : List (List κ)}
    (hE : ∀ e ∈ cert.edges, ∃ i j, name i = e.1 ∧ name j = e.2 ∧ Tangent A.center i j)
    (hanch : ∀ t ∈ mergeAnchors cert.steps, ∀ i j, name i = t.1 → name j = t.2.1 →
      dist (A.center i) (A.center j) = 2 * t.2.2)
    (h : mergeClusters cert = some cs) : ∀ c ∈ cs, IsClusterList A name c := by
  refine isClusterList_mergeFrom hinj hE cert.steps _ cs (fun c hc => ?_) hanch h
  rw [mergeAtoms, List.mem_map] at hc
  obtain ⟨e, he, rfl⟩ := hc
  obtain ⟨i, j, hi, hj, ht⟩ := hE e he
  exact isClusterList_pair hinj hi hj ht

/-! ## Soundness of the checker -/

/-- **A merge certificate proves rigidity.** The caller supplies two kinds of geometric fact —
that every listed contact is a contact, and one distance for each R3 step — and a list `all` of
names covering every circle. Everything else is combinatorics, checked by `checkMerge`. -/
theorem isRigid_of_checkMerge [Finite ι] [DecidableEq κ] (hinj : Function.Injective name)
    {cert : MergeCert κ} {all : List κ} (hall : ∀ i : ι, name i ∈ all)
    (hE : ∀ e ∈ cert.edges, ∃ i j, name i = e.1 ∧ name j = e.2 ∧ Tangent A.center i j)
    (hanch : ∀ t ∈ mergeAnchors cert.steps, ∀ i j, name i = t.1 → name j = t.2.1 →
      dist (A.center i) (A.center j) = 2 * t.2.2)
    (h : checkMerge cert all = true) : A.IsRigid := by
  rw [← rigidIn_univ_iff]
  rcases hm : mergeClusters cert with _ | cs
  · simp only [checkMerge, hm] at h
    exact absurd h (by simp)
  rcases hl : cs.getLast? with _ | cl
  · simp only [checkMerge, hm, hl] at h
    exact absurd h (by simp)
  simp only [checkMerge, hm, hl, List.all_eq_true] at h
  have hcl : IsClusterList A name cl :=
    isClusterList_mergeClusters hinj hE hanch hm cl (List.mem_of_getLast? hl)
  have huniv : namedSet name cl = (Set.univ : Set ι) := by
    ext i
    simp only [namedSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact of_decide_eq_true (h _ (hall i))
  rw [← huniv]
  exact hcl.2

/-- **A merge certificate written in terms of the circles themselves proves rigidity.** The
`name = id` case of `Arrangement.isRigid_of_checkMerge`. -/
theorem isRigid_of_checkMerge_self [Finite ι] [DecidableEq ι] {A : Arrangement ι}
    {cert : MergeCert ι} {all : List ι} (hall : ∀ i : ι, i ∈ all)
    (hE : ∀ e ∈ cert.edges, Tangent A.center e.1 e.2)
    (hanch : ∀ t ∈ mergeAnchors cert.steps,
      dist (A.center t.1) (A.center t.2.1) = 2 * t.2.2)
    (h : checkMerge cert all = true) : A.IsRigid :=
  isRigid_of_checkMerge (name := id) Function.injective_id hall
    (fun e he => ⟨e.1, e.2, rfl, rfl, hE e he⟩)
    (fun t ht i j hi hj => by
      simp only [id] at hi hj
      subst hi
      subst hj
      exact hanch t ht) h

end Arrangement

/-! ## The lattice layer -/

/-- Lattice points `v` and `w` with `eNorm (v - w) = k ^ 2` are `2 * k` apart: the squared
distance is `4 * eNorm`, so it is `(2 * k) ^ 2`. This is the arithmetic form of the one distance
an R3 step demands. -/
theorem dist_latticePoint_eq_two_mul {v w : ℤ × ℤ} {k : ℕ} (h : eNorm (v - w) = (k : ℤ) ^ 2) :
    dist (latticePoint v) (latticePoint w) = 2 * k := by
  have hsq := dist_latticePoint_sq v w
  rw [h] at hsq
  push_cast at hsq
  have h0 := dist_nonneg (x := latticePoint v) (y := latticePoint w)
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hfac : (dist (latticePoint v) (latticePoint w) - 2 * k) *
      (dist (latticePoint v) (latticePoint w) + 2 * k) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with hz | hz
  · linarith
  · have : (k : ℝ) = 0 := by linarith
    linarith

/-- **The lattice checker.** `checkMergeL l cert` asks that every contact the certificate lists
join two points of `l` at `eNorm` one, that the anchor distance of every R3 step is a perfect
square of the right size, and that the certificate merges to a cluster containing every point of
`l`. Nothing geometric is left for the caller, so
`Arrangement.isRigid_ofLattice_of_checkMergeL` closes by `decide`. -/
def checkMergeL (l : List (ℤ × ℤ)) (cert : MergeCert (ℤ × ℤ)) : Bool :=
  cert.edges.all (fun e =>
      decide (e.1 ∈ l) && decide (e.2 ∈ l) && decide (eNorm (e.1 - e.2) = 1)) &&
    (mergeAnchors cert.steps).all (fun t => decide (eNorm (t.1 - t.2.1) = (t.2.2 : ℤ) ^ 2)) &&
    checkMerge cert l

namespace Arrangement

/-- **A lattice merge certificate proves rigidity**, with no geometric hypothesis: the circles are
named by their lattice points, and both of the obligations of
`Arrangement.isRigid_of_checkMerge` are discharged by integer arithmetic. -/
theorem isRigid_ofLattice_of_checkMergeL {l : List (ℤ × ℤ)} (hl : l.Nodup)
    {cert : MergeCert (ℤ × ℤ)} (h : checkMergeL l cert = true) :
    (ofLattice l hl).IsRigid := by
  rw [checkMergeL, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hed, han⟩, hchk⟩ := h
  refine isRigid_of_checkMerge (name := fun i => l.get i) (fun i j hij => hl.get_inj_iff.mp hij)
    (fun i => List.get_mem l i) (fun e he => ?_) (fun t ht i j hi hj => ?_) hchk
  · have hb := hed e he
    rw [Bool.and_eq_true, Bool.and_eq_true] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    obtain ⟨i, hi⟩ := List.get_of_mem (of_decide_eq_true h1)
    obtain ⟨j, hj⟩ := List.get_of_mem (of_decide_eq_true h2)
    refine ⟨i, j, hi, hj, ?_⟩
    rw [tangent_ofLattice_iff hl, hi, hj]
    exact of_decide_eq_true h3
  · have h3 := of_decide_eq_true (han t ht)
    rw [← hi, ← hj] at h3
    exact dist_latticePoint_eq_two_mul h3

end Arrangement

/-! ## `O11`, re-certified by a certificate -/

/-- The nineteen contacts of `O11`: nine inside the left chevron (circles `0, …, 5`), nine inside
the right chevron (circles `6, …, 10` and the hinge `5`), and the bar between circle `0` and
circle `6`. See `Arrangement.o11_tangent_iff`. -/
def o11MergeEdges : List (Fin 11 × Fin 11) :=
  [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5),
    (6, 7), (6, 8), (7, 8), (7, 9), (8, 9), (8, 10), (5, 8), (9, 10), (5, 10),
    (0, 6)]

/-- A merge certificate for `O11`. Steps `1`–`4` build the left chevron out of its contacts
(a triangle, then three Henneberg steps, each an application of R2 with two atoms); steps `5`–`8`
build the right chevron the same way; step `9` is the ring of the two chevrons and the bar, the
three shared circles being the hinge `5`, the near end `6` and the far end `0`. That last step is
exactly the one `Arrangement.o11_isRigid_of_cluster` makes by hand. -/
def o11MergeCert : MergeCert (Fin 11) where
  edges := o11MergeEdges
  steps :=
    [.r2 0 2 1 2 0 1,
      .r2 19 3 4 3 2 1,
      .r2 20 5 7 4 3 2,
      .r2 21 6 8 5 4 2,
      .r2 9 11 10 8 6 7,
      .r2 23 12 13 9 8 7,
      .r2 24 14 16 10 9 8,
      .r2 25 15 17 5 10 8,
      .r2 22 26 18 6 0 5]

namespace Arrangement

/-- **`O11` is rigid**, by a merge certificate. The kernel checks the combinatorics of
`o11MergeCert`; the only geometry is that the nineteen listed pairs are contacts, which is
`Arrangement.o11_tangent_iff` and a `decide` on `o11Contact`. All nine steps are R2, so the
certificate demands no distances.

Compare `Arrangement.o11_isRigid_of_cluster`, which feeds the two chevrons in as rigid bodies by
`Arrangement.rigidIn_of_comap` and then applies R2 once. The certificate does not know about
bodies: it builds each chevron from its contacts instead. -/
theorem o11_isRigid_of_mergeCert : o11.IsRigid := by
  have hcontact : o11MergeEdges.all (fun e => decide (o11Contact e.1 e.2)) = true := by
    decide +kernel
  refine isRigid_of_checkMerge_self (cert := o11MergeCert) (all := List.finRange 11)
    (fun i => List.mem_finRange i) (fun e he => ?_) (fun t ht => ?_) (by decide +kernel)
  · exact (o11_tangent_iff _ _).2 (of_decide_eq_true (List.all_eq_true.mp hcontact e he))
  · simp [mergeAnchors, o11MergeCert, MergeStep.anchors] at ht

end Arrangement

/-! ## The flower, re-certified by a lattice certificate -/

/-- The twelve contacts of the flower (`flowerSites`): the six spokes from the middle circle
`(0, 0)`, and the six sides of the hexagon of outer circles. -/
def flowerMergeEdges : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((0, 0), (1, 0)), ((0, 0), (0, 1)), ((0, 0), (-1, 1)), ((0, 0), (-1, 0)), ((0, 0), (0, -1)),
    ((0, 0), (1, -1)),
    ((1, 0), (0, 1)), ((0, 1), (-1, 1)), ((-1, 1), (-1, 0)), ((-1, 0), (0, -1)),
    ((0, -1), (1, -1)), ((1, -1), (1, 0))]

/-- The steps of the flower certificate: four R2 steps that add outer circles one at a time
around the middle circle, one R1 step that glues two wedges sharing the middle circle `(0, 0)`
and the outer circle `(-1, 1)`, and a last R2 step. -/
def flowerMergeSteps : List (MergeStep (ℤ × ℤ)) :=
  [.r2 0 6 1 (0, 1) (0, 0) (1, 0),
    .r2 12 7 2 (-1, 1) (0, 0) (0, 1),
    .r2 2 8 3 (-1, 0) (0, 0) (-1, 1),
    .r1 13 14 (0, 0) (-1, 1),
    .r2 15 9 4 (0, -1) (0, 0) (-1, 0),
    .r2 16 10 5 (1, -1) (0, 0) (0, -1)]

/-- A lattice merge certificate for the flower, using R1 and R2 only. -/
def flowerMergeCert : MergeCert (ℤ × ℤ) where
  edges := flowerMergeEdges
  steps := flowerMergeSteps

/-- The flower certificate with one R3 step added: the taut chain `(1, 0), (0, 0), (-1, 0)` across
the middle of the flower, two contacts spanning the distance `4 = 2 · 2` between two opposite
outer circles (`eNorm ((1, 0) - (-1, 0)) = 4 = 2 ^ 2`).

The step is *redundant*: its three circles are already in the cluster it merges into, so the
cluster does not grow. It is here to exercise R3 and its arithmetic side condition, and there is
no alternative on the lattice: according to the exploratory census, R1 and R2 alone already build
every rigid lattice arrangement of at most `19` circles, so no small lattice example needs R3.
A chain that would really do work has to have an intermediate circle reachable by no Henneberg
step, which forces a much larger arrangement. -/
def flowerChainMergeCert : MergeCert (ℤ × ℤ) where
  edges := flowerMergeEdges
  steps := flowerMergeSteps ++ [.r3 17 (1, 0) [(0, 0), (-1, 0)]]

namespace Arrangement

/-- **The flower is rigid**, by a lattice merge certificate with no geometric hypothesis: the
kernel checks `checkMergeL flowerSites flowerMergeCert`, contacts and all. Compare
`Arrangement.flower_isRigid`, which uses a build certificate (a sequence of Henneberg steps). -/
theorem flower_isRigid_of_mergeCert : flower.IsRigid :=
  isRigid_ofLattice_of_checkMergeL flowerSites_nodup (cert := flowerMergeCert) (by decide +kernel)

/-- **The flower is rigid**, by a lattice merge certificate that also uses R3. See
`flowerChainMergeCert` for why its chain step is redundant. -/
theorem flower_isRigid_of_mergeCert_chain : flower.IsRigid :=
  isRigid_ofLattice_of_checkMergeL flowerSites_nodup (cert := flowerChainMergeCert)
    (by decide +kernel)

end Arrangement

end RigidArrangements
