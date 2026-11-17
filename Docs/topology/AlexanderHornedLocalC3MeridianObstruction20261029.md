# Local C3-equivariance obstruction for the native ternary meridian

Date: 2026-10-29. Scope: PR #1244, native ternary satellite (not the classical binary Hatcher satellite).

The exact bonding word is `w=[a,b][b,c]=a b A c B C` (uppercase denotes inverse).
Let `rho(a)=b, rho(b)=c, rho(c)=a`. Then `rho(w)=b c B a C A`.
Both words are cyclically reduced of length six. By the free-group conjugacy criterion,
two cyclically reduced words are conjugate iff they are cyclic rotations.
The six cyclic rotations of `w` do **not** contain `rho(w)`, nor does
the inverse-conjugacy class contain `rho(w)`.

**Conditional no-go theorem.** Let the child-complement stage group have a
free meridian chart `F(a,b,c)`. Suppose the parent meridian maps to `w`,
and a proposed local order-three geometric symmetry acts on this chart by
the pure cyclic permutation `rho`, while preserving the parent's peripheral
conjugacy class. Then no equivariant stage-meridian naturality square exists.
The same conclusion holds if parent orientation reversal is allowed.

**Important limit.** This does NOT prohibit an outer `C3` that permutes three
complete root sectors while each sector contains its own ternary refinement.
It also does not rule out more complicated order-three automorphisms that
are not pure cyclic permutations of the chosen based child meridians.
The distinction is critical when specifying G4–G6 and their basepoint paths.

**Executed exact check:** `python3 scripts/alexander_horned_local_c3_meridian_obstruction.py`
checks the reduced words, order-three rotation and conjugacy/non-conjugacy.
Python execution supports only free-word assertions. It does not construct
a cap-relative PL isotopy, embedded punctured torus, wild limit, exterior
fundamental group, or Agda kernel certificate.

**Attribution:** classical free-group cyclic conjugacy criterion; original
Alexander/Hatcher wild-embedding theory; native ternary bonding-map ownership
and source-specific audit in #1244. Preserve separate #1414 polynomial
monodromy, #1405 sonic T15/T16, existing pants owners and prior Ibrahim
Monster 3B attribution. No same-object promotion or ESD edits.
