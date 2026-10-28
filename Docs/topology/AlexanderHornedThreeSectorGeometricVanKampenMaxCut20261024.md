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


## 2026-10-25 source-supported inward cap + literal separator sphere breakthrough

**Primary-source progress:** Franca Lippert, *The Alexander Horned
Sphere and Bing's Hooked Rug*, §2.1–§2.2 (Figure 2, pp. 2–4),
https://www.maths.gla.ac.uk/~mpowell/WriteUp_Franca.pdf,
describes horn-stage homeomorphisms becoming the identity
away from shrinking attachment support; the wild sphere is
locally flat off its Cantor ends. Hatcher, *Algebraic Topology*,
Example 2B.2, pp. 170–172 gives the genuine individual
exterior meridian/commutator van Kampen group.

Consequently we can choose a classical supported Alexander
construction that leaves an initial round B0 inward cap
unchanged. New
`scripts/alexander_horned_supported_stable_cap_certificate.py`
checks explicit coordinates for B0 radius 3/4 in a unit
reference satellite:
  Phi(u,v,s)=(-sqrt((3/4)^2-u²-v²)+s,u,v),
  u²+v²<=1/16, |s|<=1/8.
It is a genuine local TWO-SIDED collar with an inverse
chart, not a symbolic `ClopenWitness` label.
The corrected spoke endpoint t=8.5 with disk radius
1/4 has squared satellite-centred norm 5/16<9/16,
so overlaps the ACTUAL cap-preserved wild B0, not
merely the outer reference unit container.
The local exact script passed 797 rational chart tests.
The source-supported infinite horn attachments still
have to be instantiated to declare an executable
infinite-coordinate embedding.

A much sharper geometric van Kampen separator is now
available: three literal disjoint spheres
  S_i={|x-9e_i|=4}.
Their *only* contact with the constructed solid is the
respective straight spoke, and on each sphere the
intersection is the single transverse disk GRAPH
  t=9-sqrt(16-u²-v²),   u²+v²<=1/16.
Its near axial range is 5<=t<8.5. The far root
is outside the tube; all other reference balls/tubes
lie beyond the sphere. Radius-1/4 collars around the
three S_i are disjoint. New
`scripts/alexander_horned_three_sector_separator_spheres.py`
and an independent exact-Fraction local equivalent
passed 197 rational cross-sectional checks; all-radius
claims follow from exact monotone square-root bounds.

Thus `S_i∩E=S²\closed(D²)`, an OPEN DISK, so the
exterior open-cover overlap is simply connected.
This is the proper geometric van Kampen cut; a PLANE
minus disk would instead have pi1=Z and must not
be used as though it were simply connected.

New comprehensive source-attributed proof note:
`Docs/topology/AlexanderHornedSupportedCapSeparatorVanKampen20261025.md`.
It spells out how a threefold collared boundary
connected sum can yield B3 and, using the standard
unknotted-tree-neighbourhood/side-cap equivalences,
`pi1(E)=G_A*G_A*G_A` with outer C3.
This is a **paper-level source-supported geometric
proof scheme** with exact local geometry; the native
infinite horn support map and all ambient deformation
retractions are NOT machine-proved or explicitly
coordinate-constructed in the repo.

This discharges the earlier vague *existence of a tame
cap as an unexplained input* by pointing to and using the
actual supported original horn construction. The
remaining max-cut is no longer 'find separating spheres',
but instantiate its *supported infinite attachment*
and the complement-piece homeomorphisms as concrete
same-object maps. No Agda/CI work per user request.


## 2026-10-25 completed orbifold C3 semantic bridge

The genuinely EXTERNAL order-three subgroup has an
actual topological interpretation once the wild
exterior E is realized as R-invariant. The point
x0=(20,20,20) is fixed by the ambient R and lies
outside the compact C3-symmetric scaffold.
For the global quotient orbifold `[E/C3]`,
the Borel fibre sequence `E->E_hC3->BC3`
has a section induced by x0. Hence
  pi1^orb([E/C3]) ~= pi1(E) rtimes C3.
Under the supported Hatcher triple-gluing
identification this becomes
  (G_A*G_A*G_A) rtimes C3.
The source `pi1(E)` remains torsion-free;
external finite C3 is ORBIFOLD STABILIZER data.
This is NOT generally the ordinary fundamental
group of the coarse quotient space `E/C3`.
This also clarifies the discrete spin3 lift versus
continuous 360°/720° rotation-path distinction.
Primary expository root: Caramello,
*Introduction to Orbifolds*, arXiv:1909.08699.
`scripts/alexander_horned_orbifold_split_c3.py`
locally checks the fixed-point and semidirect group
law in the exact 2I finite quotient.

Other NEW source-grounded geometric commitments:
Lippert §2.2 supplies supported horn homeomorphisms,
preserving an inward tame cap of B0; a real radius-3/4
cap chart and positive-volume collar overlap were
locally certified, as were three radius-4 separating
spheres with ONE transverse disk each. They yield
simply connected van Kampen overlaps
`(S²\\closed D²)×I`, rather than the non-simply
connected PLANE-minus-disk overlaps.
Complete report:
`Docs/topology/AlexanderHornedSupportedCapSeparatorVanKampen20261025.md`.

The paper-level wild topology still depends on the
classical supported Hatcher construction and standard
tree/collar neighbourhood equivalences; local Python
does not turn these into Agda kernel proofs. No CI
or Agda typecheck was performed per user request.


## 2026-10-25 roadmap reset: FINITE vs INFINITE physical observables

New source-audited decision report:
`Docs/topology/AlexanderHornedRoadmapRealWorldImplications20261025.md`.

**Critical Hatcher object discriminator:** `B_n` is a
locally-flat/tame finite horned BALL with simply connected
exterior (Schoenflies), whereas Hatcher's stage enclosure
`X_n` is a genus-`2^n` handlebody with nontrivial
exterior `Y_n` and `pi1(Y_n)=F_(2^n)`.
For three independent sectors, stage group rank is
`3*2^n`. The ideal limit `B=intersection X_n` is
the source of the perfect but nontrivial exterior group.
Do NOT use a finite printed B_n and falsely advertise
the complement group of X_n or the ideal limit.
Original: Hatcher Example 2B.2 (printed pp171-172)
and locally-flat Schoenflies.

**Essential noncommutation of limit/abelianization:**
Each source meridian becomes a child commutator, so
H1(Y_n)->H1(Y_(n+1)) is the ZERO map despite each
H1(Y_n)=Z^(3*2^n). Thus H1(E)=0 while
pi1(E) is nontrivial. In R3 the exterior also has
H2(E)=Z from the sphere at infinity; in S3 the
complement of the compact contractible ball is
reduced-acyclic. Do not call R3 exterior fully acyclic.

**Flat U1 vs nonabelian holonomy**:
Hom(perfect G,U1)=1; each isolated finite free stage
has nontrivial U1 characters that cannot be carried
compatibly through all commutator refinements.
In contrast existing 2I=SL2(F5) perfect quotient
has an order-six root q with q^3=-I, recursively
compatible child commutators and spin-character
Wilson trace -2. Nonflat Maxwell connections can
still have Wilson loops on contractible paths.
A one-level Q8 commutator [i,j]=-I works, but
Q8 cannot extend recursively: [Q8,Q8]=C2.
The perfect 2I target is essential for ALL scales.
Executable finite audit:
`scripts/alexander_horned_scale_holonomy_maxcut.py`.

**Actual experiment/control roadmap:** finite sculpture,
finite X_n handlebody, and unlinked/tame controls must be
labelled DIFFERENT specimens. A synthetic SU2/optical
control circuit may implement recursive commutator
identities and observe relative Wilson phases; this is
not direct observation of the infinite wild pi1.
Prior published physical feasibility roots: Lucien
Grillet's FOUR-level 20cm PLA/PVA horned sculpture,
Bridges 2022; Q. Liang et al. Nature Physics
(2024), DOI 10.1038/s41567-024-02644-4
synthetic SU2 nonabelian AB in a 1D ladder, and
Sugawa et al. npj Quantum Information (2021)
nonabelian Wilson-loop measurements.
No original DASHI experiment currently exists.

**Quantitative synthetic signature:**
`scripts/alexander_horned_su2_controls_noise_probe.py`
verifies exact quaternion algebra
`tr([A,B]) = 2-4 sin²(alpha) sin²(beta)` for
orthogonal-axis SU2 controls; at alpha=beta=pi/2
this is -2 versus commuting U1 +2. Angular control
errors change the trace; a lone global -1 spinor sign
must be measured against a reference. One SU2
commutator does not prove the whole tower's perfectness.

**Hard acceptance gates:** actual supported Hatcher
infinite horn coordinates and cap, the three piecewise
open-cover/van Kampen homotopy maps, CAD models with
known finite stage group, calibration/flatness controls,
specified Maxwell/Dirac operator and boundary data.
No implication of gravity anomalies, free energy,
superluminal communication, quantum consciousness or
new physical zero modes.

The work priority is a dual track: geometry source
same-object closure plus practical finite nonabelian
control experiment; defer Agda typecheck/CI by request.
