# Three-sector Alexander horned exterior: source-specific max-cut and geometric supplier contract

Date: 2026-10-24. PR #1244. This report corrects earlier tangent-only handle
claims and advances the ABSTRACT three-root free group from unverified stage
injections to a direct normal-form proof. It also closes the outer-C3 question
at the abstract group level. No Agda typecheck or CI was run (user preference).

## Attribution and exact primary source

Allen Hatcher, *Algebraic Topology*, Example 2B.2,
https://pi.math.cornell.edu/~hatcher/AT/AT.pdf ,
printed pp171-172 (PDF pages 179-180). Inspected in the SOURCE PDF pages.
The Hatcher 1924 root is J. W. Alexander, *An Example of a Simply Connected
Surface Bounding a Region Which Is Not Simply Connected*, PNAS 10 (1924).

IMPORTANT: Hatcher starts with `X0` a solid torus, `Y0` exterior pi1 Z,
and then `pi1(Y_n)=F_(2^n)` with meridian generator inclusion
`x -> [a,b]`. The inclusion is established geometrically by the
punctured-torus attachment, `Z-A` a ball with two straight tubes removed
and van Kampen (not just by binary count). The exterior is `union Y_n`;
compactness of loops and homotopies gives the direct limit.
The loop group is nontrivial and perfect.

Independent textbook source for free products and van Kampen:
Hatcher §1.2, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf.
See also H. Lee, *The van Kampen theorem*, 2013,
https://people.math.harvard.edu/~hirolee/pdfs/231a-35-van-kampen.pdf.
Do not mistake the compact 3-ball on the HORNED side for the
gored/non-simply-connected exterior on the OTHER side.

## Key group theorem now resolved (not an unproved analogy)

Let H_n=F_(2^n), with injective `x_i -> [x_(2i),x_(2i+1)]`.
Let G_A=colim H_n be the classical Hatcher abstract limit.
Our THREE-SECTOR tower consists of independent factors:

    G_n = F_(3*2^n)
        = H_n^(sector0) * H_n^(sector1) * H_n^(sector2),

and each transition is precisely the free product of the
three Hatcher transition maps (NO mixed-sector bonding relations).

Since free product is a coproduct and filtered colimits commute with
coproducts in the category of groups, their colimit is

    G_three = G_A * G_A * G_A,

NOT `G_A^3`. The already constructed surjection
`G_three -> (2I)^3` is a QUOTIENT (products can be quotients
of free products); likewise for `A5^3`.

An elementary ALL-STAGE injection argument avoids category
black boxes. Encode any reduced source word w on generators
(sector, binary address) by signed letters. Each positive
basis letter substitutes to four symbols

    [a_i,b_i] = a_i b_i a_i^-1 b_i^-1,

and each negative letter uses its reduced inverse
    b_i a_i b_i^-1 a_i^-1.

The two child symbols for different source generators lie in
PAIRWISE DISJOINT alphabets. Every block is cyclically reduced.
Adjacent source letters that are distinct use disjoint alphabets;
adjacent equal letters must have equal sign because the source is
reduced. Thus NO cancellation occurs between blocks and

    |expand(w)| = 4 |w|.

So `expand` is injective at EVERY depth, not only at bounded
tested levels. It also commutes exactly with the C3 sector cycle.

The local Python audit tested 18,112 reduced words at selected
ranks/depths. These are verification receipts supporting the
general normal-form proof, NOT a substitute for it.

### Strongest new result: the abstract C3 is OUTER

The cyclic rotation rho of the three free factors has rho^3=1.
Take m0!=1 in factor 0 and the canonical group retraction
p0:G_three->G_A which kills factors 1 and 2. Then

    p0(rho(m0)) = 1.

If rho were conjugation by any g in G_three, we would have

    p0(rho(m0))=p0(g) m0 p0(g)^-1 != 1,

a contradiction. The same proof applies to rho^2.
Therefore rho has EXACT order 3 in `Out(G_three)`.
This is a positive result: our cyclic symmetry is not just
address relabelling, and we never demanded a nonsplit C3 spin cover.

`scripts/alexander_horned_three_sector_outer_c3_witness.py`
checks the observer argument in the ACTUAL nonabelian
SL2(F5) quotient. An explicit order-six root q has q^3=-I
and is a commutator; all 120 conjugates of q remain
nonidentity. No claim about `Out(pi1(E_geom))` follows until
the C3-equivariant geometric same-object isomorphism exists.

The threefold free product remains perfect (abelianization zero)
and torsion-free (torsion theorem for free products of
torsion-free groups). It is residually finite through the
previously source-audited alternating-quotient/Ore argument.
None of these groups is a three-torus or a C3×Z2 group.

## Critical geometric bug fixed: tangent is NOT attached

The original
`scripts/alexander_horned_clopen_tree_handle_scaffold.py`
used thin tubes whose axial cores ran `1 <= t <= 8` from
unit central ball at 0 toward unit satellites at 9e_i.
Those cores touched each unit sphere at ONE POINT; that
was NOT a positive-area collared 1-handle attachment.
Any previous promotion claiming an already attached B3
from those constraints is INVALID.

Corrected model: radius eps=1/4, cores with
    1/2 <= t <= 17/2,
inside each coordinate axis. The COMPLETE cross-sectional
disk at each end is inside its incident unit ball, since

    (1/2)^2+(1/4)^2 = 5/16 < 1.

For a tube point outside the central ball, the axial
coordinate must be t>3/4 because
    (3/4)^2+(1/4)^2=5/8 < 1.
A point common to two distinct axis tubes would also
need that coordinate <=1/4 from the other tube's
transverse-radius bound. Contradiction. Thus exposed
tube regions are pairwise disjoint; any overlap of tubes
is contained in the central ball. Off-axis satellites
remain disjoint by the 9-1/4 coordinate gap.

The corrected original script AND a stronger regression
`scripts/alexander_horned_three_sector_geometric_vankampen_probe.py`
are committed. ALL exact rational inequalities passed
independently using local Python.

**GATE**: those calculations are for STANDARD unit satellite
balls. A Hatcher wild ball located inside such a ball is
not automatically equal to the whole unit ball, so the
tube is not thereby attached to the WILD ball. An actual
accessible tame disk and COLLATED local parametrization
of its collar are separate, mandatory geometric witnesses.

## Exact compatibility of local links and collars

The earlier unscaled linked/unlinked circles were not
confined to UNIT satellite balls. Correct that:
take local circles
    C1(t)=(2 cos t, 2 sin t,0),
    C2_h(t)=(h,1+cos t,sin t), h=1 or 5.
Apply positive scale 1/8 and outward radial translation
(1/4,0,0) relative to the satellite center.

The maximal squared satellite-centered radius of
the scaled C2_5 circle is 53/64 <1; for C2_1 it is
13/64<1; C1 is also inside the unit satellite.
All loop points have outward radial coordinate >=0,
while the inward spoke ends at radial coordinate -1/2.
They are therefore disjoint from the tube collar.

An exact signed disk-intersection calculation gives
`lk(C1,C2_1)=-1` and `lk(C1,C2_5)=0`. Orientation-
preserving R(x,y,z)=(z,x,y) clones three sectors.
These links are LOCAL CLASP MODELS only: they are not
identified with the linked actual Hatcher handles.

## Explicit REAL Euclidean nested balls for a TAME comparator

To strengthen 'prefix balls are clopen' beyond the older
`SSP369ClopenBallBridge` label constructors, the new
`scripts/alexander_horned_tame_cantor_ball_cylinders.py`
builds genuine nested EUCLIDEAN 3-balls.

A length-n binary prefix has interval
    [1/6+(1/3)*sum_(j<n)2b_j/3^(j+1), that + L_n],
    L_n = 1/3^(n+1).
The Euclidean ball has centre (interval midpoint,1/2,0)
and radius (3/5)L_n. A level-n parent has child
centres shifted by L_n/3 and child radii L_n/5;
thus child-centre-shift+radius=8L_n/15 <
parent radius=3L_n/5, STRICT containment. The two
children have disjoint closed balls, gap=4L_n/15>0.

The root Euclidean ball centre (1/3,1/2,0), radius 1/5,
is strictly inside the unit satellite and lies ABOVE
the clasp curves (root y>=3/10>1/4), and on the
outward side of the inward tube (root x>=2/15>0).
Rotation copies the system into three disjoint satellite
unit balls. Exact local code checked 511 nested balls.

This makes the key counterexample CONSTRUCTIVE:
clopen binary branching + C3 invariance + honest
nested 3D balls + disjoint geometric collars STILL
does not construct a WILD horned sphere or a nontrivial
exterior fundamental group. It is a tame Cantor comparator.

## Geometric theorem conditional on the actual gluing data

A promising source-defined construction reuses ONE
classical Hatcher horned ball `B_A`, with a standard
TAME boundary disk away from its Cantor wild points.
Place three congruent copies in the satellite charts
and rotate by R. Choose their tame disk collars facing
the central ball, and glue to a central tame ball via
the 3 disjoint spoke handles in the corrected geometry.

Under genuine collared attachment certificates, a
boundary-connected sum of four topological 3-balls along
the three-edge TREE is again a topological 3-ball.
The ambient rotation sends the chosen construction to
itself exactly, and the wild Cantor end sets remain
in the three satellite regions.

The geometric van Kampen goal has a specific separator:
each satellite neck should admit a splitting sphere
intersecting the resulting solid in a single collared
closed DISK. Its complementary part in the exterior
is simply connected. With this proved (not guessed),
an open-cover/graph-of-spaces van Kampen argument yields

    pi1(E_three) ~= G_A * G_A * G_A,

with finite-stage exterior group F_(3*2^n) and all
meridian transitions explicitly matching Hatcher.
The geometric C3 action then transports to the
already proved outer cyclic permutation.

This is a coherent geometric proof PLAN, not a new
constructed collar homeomorphism or an executed
topological van Kampen certificate.

## What is still actually open

P0: For ONE chosen Hatcher wild ball, choose a
literal tame attachment disk in its tame boundary
region and supply a local collar chart with explicit
support (rather than the ideal unit-ball overlap).
P1: Attach those three collared wild balls along
the corrected disjoint coordinate spokes and
supply the ball/homeomorphism and exterior splitting
sphere/open-cover certificates.
P2: Prove stage meridians and inclusions are exactly
the ones in Hatcher Example 2B.2, and the colimit
isomorphism is C3-equivariant.
P3: Only then identify the genuine geometric
exterior pi1, noninner C3 action, spin-equivariant
Dirac operators and physical spectral constraints.

DONE: exact free word injection and free-product
colimit algebra; noninner C3 by retraction; corrected
3D collar geometry; local Hopf clasp compatibility;
actual nested Euclidean tame Cantor ball control.

Per user preference no Agda typechecking or CI attempted.
Do not mislabel all-stage algebraic arguments as
Agda kernel proofs or compare unrelated 'E_n'/Monster
objects by matching 3, 12, 27, 120 or 360 numbers.
