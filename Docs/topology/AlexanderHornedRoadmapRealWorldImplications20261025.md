# Alexander horned three-sector programme — mathematical max-cut, phase gates, and real-world steelman

Updated 2026-10-25 (AEST). Existing repo chboishabba/dashi_agda PR #1244.
This is an attribution-preserving mathematical/experimental roadmap,
NOT a claim to have manufactured the infinite wild surface, detected
an exotic physical effect, or kernel-proved infinite geometry.

## Executive conclusion

The most interesting *real-world* discriminator is not C3 splitting
or an arbitrary spin-720 trick. It is the finite-to-infinite distinction:

- A finite **tame ball** B_n, including a smooth sculpted horned ball,
  has a simply connected exterior by tame Schoenflies.
- The finite **enclosing handlebody** X_n in Hatcher's construction
  has an exterior Y_n with pi1(Y_n)=F_(2^n) and H1(Y_n)=Z^(2^n).
- The ideal infinite wild ball B=intersection X_n has an exterior
  E=union Y_n with nontrivial PERFECT pi1.
  Our three-sector source, after the supported geometric gluing, is
  GA*GA*GA and stage ranks 3*2^n.

The bonding map is generator -> [new left,new right]. Consequently
its induced map H1(Y_n)->H1(Y_(n+1)) is ZERO at each stage.
Thus H1(E)=colim H1(Y_n)=0 even though all finite Y_n
have nonzero H1. This is the algebraic mechanism behind the
limit's topological surprise, not simply 'lots of twisting'.

Do not claim H2(R3\\B)=0! For a compact 3-ball B,
Alexander duality applied to the TWO components of B cup
{infinity} gives H2(R3\\B;Z)=Z; H1=0. In S3\\B,
the reduced homology groups vanish because B is contractible.
This is independent of embedding wildness and matches the
homology of the ROUND ball exterior. The nonabelian pi1
difference is what standard homology misses.

## Primary-source audit and attribution

1. J. W. Alexander, *An Example of a Simply Connected Surface
   Bounding a Region Which Is Not Simply Connected*, PNAS (1924).
2. A. Hatcher, *Algebraic Topology*, Example 2B.2, actual PDF
   pp.178–180 (printed pp.170–172),
   https://pi.math.cornell.edu/~hatcher/AT/AT.pdf.
   Explicit X_n decreasing handlebodies, Y_n increasing exteriors,
   genuine punctured torus van Kampen, injective F_(2^n)
   ->F_(2^(n+1)), and perfect limit pi1. The construction
   of B_n as an expanding tame ball is NOT the same as X_n.
3. F. Lippert, *The Alexander Horned Sphere and Bing's Hooked Rug*,
   §§2.1–2.3,
   https://www.maths.gla.ac.uk/~mpowell/WriteUp_Franca.pdf.
   Horn-stage support, pillboxes and locally flat patches outside
   the Cantor wild set. The three-sector 9e_i choice belongs to
   THIS repo, not Lippert or Hatcher.
4. M. Brown generalized locally-flat Schoenflies theorem,
   modern precise exposition:
   https://www.maths.gla.ac.uk/~mpowell/Topological-manifolds-lecture-notes-after-seminar.pdf.
   A finitely printed smooth/tame S² boundary CANNOT have the
   wild exterior pi1, however close it visually resembles B.
5. Lucien Grillet, *3D Printed Models of Wild Spheres*,
   Bridges 2022, pp413–416,
   https://archive.bridgesmathart.org/2022/bridges2022-413.pdf.
   Describes a FOUR-level, 20 cm physical horned-sphere sculpture,
   43% refinement scale, printed in PLA with soluble PVA supports.
   This is a real decorative finite model, not an experiment
   measuring an infinite-limit group or exotic holonomy.
6. Q. Liang et al., *Chiral dynamics of ultracold atoms under a
   tunable SU(2) synthetic gauge field*, Nature Physics 20
   (2024), 1738–1743, doi:10.1038/s41567-024-02644-4.
   Observed non-Abelian Aharonov–Bohm behaviour on a synthetic
   single plaquette. This demonstrates experimental feasibility
   of non-Abelian control/observation, NOT horned-sphere physics.
7. S. Sugawa et al., *Wilson loop and Wilczek–Zee phase from a
   non-Abelian gauge field*, npj Quantum Information 7,144
   (2021), doi:10.1038/s41534-021-00483-2.
   Another prior original finite non-Abelian Wilson measurement.
8. Flat connection/holonomy correspondence:
   standard gauge theory for connected manifolds, e.g.
   D. Duncan, *Flat connections and holonomy*,
   https://educ.jmu.edu/~duncandl/FlatHolonomy.pdf.
   For a FLAT connection, holonomy factors through pi1;
   for CURVED connections Wilson loops can be nontrivial
   even on contractible loops.

## A genuinely falsifiable finite algebraic signature

Define source stage F_(3*2^n), generator x_{c,w}.
Bonding map:
    phi_n(x_{c,w})=[x_{c,w0},x_{c,w1}],
with pairwise disjoint child alphabets. It is injective
(normal-form length expansion exactly fourfold).
All abelian characters phi_n^*(chi_{n+1}) are TRIVIAL,
because each phi_n generator is a commutator.

A flat U(1) connection on the final perfect group G has
ONLY trivial holonomy representation
  Hom(G,U1)=1.
But an individual stage F_(3*2^n) admits many nontrivial
U(1) characters! None extend to the entire compatible
tower with nontrivial root image. This is NOT saying
an ordinary Maxwell magnetic field must vanish:
nonflat electromagnetic curvature produces ordinary
Wilson loops even when Hom(pi1,U1)=1.

The nonabelian counterexample is CONCRETE:
2I=SL2(F5) is a finite perfect group with all 120
elements realized as commutators, as already verified
by `scripts/alexander_horned_spin_icosahedral_bridge.py`.
An order-six root q in the existing witness has q^3=-I;
child labels a,b can be chosen with [a,b]=q,
and every descendant chosen recursively.
Thus G->2I is compatible at all depths. Under the
classical defining SU2 spin representation of 2I,
the central -I has Wilson trace -2 versus +2 at +I.
It is an actual DIFFERENCE in gauge-invariant
conjugacy-class trace, not a scalar group character.

We also checked why the older Q8 work alone is not
enough: [i,j]=-I provides a one-step nonabelian
commutator, but [Q8,Q8]={+I,-I}, so the noncentral
child images i,j cannot themselves be recursively
commutators in Q8. Moving from solvable Q8 to perfect
2I is necessary for full horn-tower compatibility.
This is a genuine physical-model selection criterion.

New reproducible finite test:
`scripts/alexander_horned_scale_holonomy_maxcut.py`.
An equivalent independent local Python file was executed
successfully: six stage H1-zero maps, 120/120 2I
commutator coverage, 7 levels of consistent 2I labels,
Q8 failure at second depth and q^3=-I.

## Recommended real-world steelman: a three-control comparison

**A. Finite geometry / topological control (print and inspect).**
Construct symmetric three-sector specimens:
(1) a tame rounded horned ball B_n;
(2) Hatcher's HANDLEBODY ENCLOSURE X_n with literal
    paired linked handles and correctly defined exterior;
(3) an unlinked control with same thickness, scale,
    number of ends and C3 symmetry.

Inspect links, connectedness and exterior stage-meridian
loops directly or with CAD knot/link data. Do not say a
finite tame B_n realizes nontrivial wild exterior pi1.
The sculpture/print has the role of a precise finite
geometric analogue.

**B. Gauge emulator / flat SU2 lane (better first experiment).**
Use a two-component unitary internal degree of freedom
(optical Jones modes, trapped-atom synthetic SU2, or a
controlled quantum unitary circuit).
Implement child transports a,b and their commutator
  W=a b a^-1 b^-1
as a programmable loop or graph gauge link, and
iterate at several finite binary refinement depths.

Controls:
  (i) matched commuting U1 channels => W=I exactly;
 (ii) Q8 i,j => W=-I for first depth but recursion fails;
(iii) full 2I-compatible stagewise word assignments
      => nontrivial commutator and q^3=-I
      consistently across all selected depths;
 (iv) switched link order/flattened curvature/control
      to distinguish path sensitivity from an artefact.

Measure SU2 Wilson trace or interferometric relative
phase against a reference arm. A central -I is not
visible as a sign in a single isolated ray; it is
visible in a RELATIVE interferometric phase.
SU2 Jones optical controls can also reproduce this
algebra classically; it is not by itself proof of
spin-1/2 particles or new quantum physics.

To claim FLAT TOPOLOGICAL HOLONOMY, the physical
implementation must provide a domain/graph carrying
the prescribed noncontractible paths AND verify local
flatness (plaquette identities) away from excluded flux.
Simply implementing noncommuting gates in a simply
connected physical setup demonstrates a useful
synthetic NONABELIAN CONTROL analogy, not the
fundamental group of wild 3-space.

**C. Unbounded-depth mathematical/geometric lane.**
Build one supported Hatcher ball with explicit horn
pillbox homeomorphisms, preserved inward tame cap,
the exact radius-4 separating spheres from existing
local scripts, and complete all complement-piece
homotopy equivalences. Prove the threefold glued ball
homeomorphic B3, pi1(E)=GA*GA*GA and the geometric
C3 action outer (the abstract version is already proved).
This would be a TOPOLOGY theorem, not evidence of
a physical non-Abelian gauge field.

## Physical scale reality

The original 2022 sculpture used 20 cm, 4 levels, scaling
0.43. For a characteristic scale L0=200 mm and model ratio
r=0.43, illustrative L_n=L0*r^n and number of marked horn
tips N_n=3*2^n. At n=4, L≈6.84 mm and N=48;
at n=8, L≈0.234 mm and N=768. Those L_n are only
DIMENSIONLESS GEOMETRIC ENVELOPE estimates; wall
thickness, horn gap, support removal, surface roughness,
wavelength and manufacturing resolution are independent
necessary limits.

The fully expanded source root commutator word has
length 4^n at stage n. However its VALUE can be
computed with a recursive gate/circuit (without
printing the entire exponentially long word in
memory). For actual physical paths, the traversal
resource cost still scales and needs independent
error/visibility budgeting.

The finite limit is TOPOLOGICALLY DISCONTINUOUS:
even perfect-looking finite smooth B_n is tame;
no finite additive manufacturing tolerance makes its
flat exterior holonomy represent the infinite wild
ball's perfect pi1. The relevant observable must
be defined at finite cutoff, and extrapolation
must be framed as a mathematical limit.

## Risks and actual falsifiers

1. **Embedding mismatch**: finished three-sector surface
   not a B3 / attaching collars fail -> no claimed
   GA*GA*GA geometry. Acceptance: explicit ambient
   maps plus simply-connected cut-sphere overlaps.
2. **Finite-stage category mistake**: test on B_n
   but analyze X_n -> incorrect topology. Acceptance:
   CAD model labels side/exterior and verifies handle
   genus and pi1 input.
3. **Fake nonabelian signature**: nontrivial U1 signal
   from local curvature; SU2 signal from uncontrolled
   field gradients -> does not identify topological
   holonomy. Acceptance: independent flux/flatness and
   matched-geometry controls.
4. **Loss of global compatibility**: arbitrary
   stage-by-stage SU2 matrices with no
   [child,child]=parent relation -> not a horn tower.
   Acceptance: explicit algebraic consistency at
   EVERY stage tested, with calibrated error.
5. **Unobserved relative phase**: -I is physically a
   global sign on an isolated spinor. Acceptance:
   reference-arm interference/Wilson trace, not
   populations alone.
6. **Overclaimed general physics**: no evidence this
   implies gravitational anomalies, superluminal
   transport, fusion confinement, free energy, or
   quantum consciousness. Gauge experiments here
   benchmark nonabelian interference and topology
   simulation only.
7. **Misuse of p-adic endpoints**: K=C3×Z2
   is intrinsic wild-end address topology; it is
   NOT the topological type of connected E or a
   nontrivial pro-2 quotient of perfect pi1.

## Phases and measurable acceptance gates

| Phase | Concrete delivery | Accepted when | Status |
| --- | --- | --- | --- |
| 0 — provenance/claim ledger | Hatcher/Lippert/Grillet/gauge papers and prior DASHI proof owners | Original source, interpretation and proof status distinct | This report |
| 1 — algebra and representation | Free-stage F_(3*2^n), 2I, A5, spin12, H1 and characters | Exact meridian recursion, quotient and spin-sign tests | Finite local PASS; abstract math |
| 2 — embedded geometry | Explicit supported wild sphere B3 with collars | B3 homeomorphism, R(B)=B, genuine wild Cantor boundary | Conditional classical construction; full coordinate map still open |
| 3 — geometric pi1 | Three disjoint sphere cuts, open-cover/van Kampen maps | Actual pi1(E)=GA*GA*GA equivariantly | Sphere equations PASS; full piece retractions open |
| 4 — finite physical prototype | B_n vs X_n vs unlinked control | Measured CAD/geometry and resolution, without wild-limit claim | External precedent exists; project specimen not built |
| 5 — synthetic gauge test | Controlled abelian/nonabelian stage words | Commutator and Wilson phase with flatness/curvature controls | Real external precedent, not project experiment |
| 6 — physical field theory | Classical/quantum PDE and boundary conditions | Self-adjoint/specified Dirac or Maxwell domain plus measured predictions | Not established |

Pareto recommendations:
P0a mathematical: close the exact supported Hatcher horn
coordinate construction and piecewise exterior homotopy
maps (phase 2–3).
P0b practical: run the finite 2I vs U1 synthetic
commutator protocol and its controls (phase 5)
WITHOUT waiting for an infinite physical object.
P1: CAD stage pairs B_n/X_n and report actual
fabrication dimensions/flux-network scale (phase 4).
P2: if one wants genuine physical predictions,
construct a Maxwell/Dirac/Schrödinger operator with
boundary conditions and a controlled cutoff.
P3: leave 3B Monster, exceptional En, p-adic phases
as carefully marked possible MODEL REUSE, not
evidence of new physical behaviour.

## What would count as a novel result?

The classical Alexander/Hatcher perfect group is NOT new.
The classical SU2 spin-720, 2I representation and the 2024
nonabelian AB experiment are NOT new.
A defensible research contribution would be either:
(a) an explicit source-correct equivariant wild 3-ball
with provably outer geometrical C3 and specified
complement decomposition;
(b) a new finite-depth measurement/protocol showing
scale-compatible NONABELIAN meridian holonomy while
all compatible Abelian characters die, with quantified
noise, controls, cutoff and a meaningful comparison
to previously published nonabelian AB implementations;
(c) an independent spectral/scattering prediction
derived from a specified PDE and falsified/confirmed
on finite stage objects. None of (a)–(c) has yet
been delivered as a complete experimental result.

**Status discipline**: Python finite checks are finite
checks. Mathematical deductions can use credited
classical theorems. Original repo authorship and
same-object evidence remain separate. No Agda
kernel or CI activity by explicit user request.
