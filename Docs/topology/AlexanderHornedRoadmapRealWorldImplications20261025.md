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


## Extra spin / Chern class completion: gauge sectors vs geometry

This is a significant consequence of the RIGHT
Alexander-duality groups, not a speculative physical mechanism.

E=R3\\B is an open orientable smooth 3-manifold
(Euclidean R3 restricted away from a compact topological ball).
It inherits a globally trivial tangent bundle and
its ambient Euclidean spin structure. Since
H1(E;Z)=0, universal coefficients give
H^1(E;Z/2)=Hom(H1,Z/2)=0. Spin structures on
an oriented spin manifold form a TORSOR for
H^1(E;Z/2), so E has exactly ONE spin structure
up to isomorphism. The exterior's nontrivial
perfect pi1 does NOT give alternative Z2-valued
spin twists around its nontrivial loops.

In the globally fixed Euclidean frame the ordinary
Levi-Civita connection (and its lifted spin
connection) is flat with trivial loop holonomy.
The sign change in a 360-degree PATH OF ROTATIONS
in SO3 is NOT automatically holonomy around a
spatial loop in this flat exterior. It is the
Spin3 double-cover path phenomenon, a distinct
object. Thus a nontrivial 2I flat monodromy
would be an ADDITIONAL chosen SU2 gauge connection,
not forced by wild embedding or the metric.

On the other hand, for B compact contractible,
H^2(E;Z)=Z as proved from Alexander duality
for B union {infinity}. Complex line bundles
(principal U1 bundles) over E are classified
by c1 in H^2(E;Z)=Z. Nonzero classes can
carry curvature/monopole-like magnetic flux
through a surrounding S2. They cannot carry
FLAT U1 connections: a flat bundle's integral
c1 is torsion, and Z has no nonzero torsion.
This is the same flux classification available
in the exterior of a ROUND ordinary ball,
and therefore is NOT a distinctive wild topology
observable. It also reconciles 'no flat Abelian
holonomy' with 'nonzero physical Maxwell flux'.

Original/reference ownership:
- Hatcher, Example 2B.2 and Alexander duality.
- John Baez, *Torsors* (spin structures as H1(Z/2) torsor):
  https://math.ucr.edu/home/baez/torsors.html
- Standard locally-flat 3D geometry/tangent frame:
  Dionne Ibarra, *A note on a short proof of the
  parallelizability of orientable 3-manifolds*,
  arXiv:2207.12149 (stronger theorem than needed;
  our E subset R3 is automatically parallelized).
- Laurentiu Maxim, notes on circle bundles:
  https://web.math.wisc.edu/~lmaxim/754notes.pdf,
  line bundles classified by H2 integral.
- Flat line-bundle curvature class: de Rham
  image of c1 vanishes, so c1 is torsion;
  here only c1=0 can be flat.

Acceptance guardrail:
Distinctive wild-spin effects require a specific
nonabelian connection AND measurable Wilson/Dirac
effects with controlled locality and gauge coupling.
Unique spin structure does not erase the existence
of nontrivial SU2 FLAT BUNDLES (via 2I quotient);
it only rules out distinct untwisted spin
structures indexed by Hom(pi1,Z2).


## 2026-10-25 dual-track implementation max-cut — GEOMETRIC PAPER THEOREM + EXECUTED GAUGE SIMULATOR

**GEOMETRY:** New `Docs/topology/AlexanderHornedC3SameObjectGluingTheorem20261025.md` supplies the full source-attributed paper-level existence argument for a 3-sector equivariant wild B3: choose the Hatcher/Lippert horn seed with an unchanged inward tame disk, attach three rotated supported copies to the central unit ball with actual tame radius-1/4 collars, cut by three radius-4 spheres and use classical boundary-connected sum and van Kampen. The NEW explicit stereographic coordinates
  sigma(t,u,v)=(u/(t-5),v/(t-5))
map each geometric cut-sphere exterior overlap homeomorphically to the OPEN disk `|y|<16+sqrt(255)`; inverse
  t=(13+5|y|²)/(1+|y|²), u=8y1/(1+|y|²), v=8y2/(1+|y|²).
It contracts by `H_s(y)=(1-s)y`, so a collar overlap is simply connected. That removes a vague topological-overlap assumption and uses actual source-defined tubes/caps. The usual tame-collar replacement argument identifies satellite-side pi1 with original Hatcher `G_A`; the round-star control establishes central-side pi1 trivial. The cut-and-paste theorem then yields `pi1(E)=G_A*G_A*G_A` and outer C3 at a fixed basepoint. Original wild embedding / its stage theorem and standard 3-manifold lemmas remain EXTERNAL CLASSICAL theorem inputs, and an indexed infinite coordinate map / kernel proof is STILL NOT coded. Code: `scripts/alexander_horned_C3_same_object_separator_atlas.py`. Locally validated 2601 stereographic and 797 cap-chart samples, with exact rational identities and explicit inverse.

**EXECUTED SYNTHETIC SU2 GAUGE MODEL:** New `scripts/alexander_horned_c3_finite_SU2_gauge_simulator.py` constructs all 120 binary-icosahedral unit quaternions over Q(phi), checks all group products, finds exact commutator witnesses for ALL 120, selects `q=(1+i+j+k)/2` whose cube is `-1`, and assigns Hatcher child meridians compatibly through selectable finite depth. Ideal selected root-cube Wilson halftrace is `-1` for all depths; matched commuting U1 halftrace `+1`; Q8 yields central `-1` at ONE level but cannot maintain full recursion. Model applies independent gate-axis-angle noise and Bernoulli controlled-U readout shots. A locally executed source-equivalent 50-trial/300-shot/1.5deg simulation returned depth-0..5 observed halftraces `[-0.9999,-0.9995,-0.9955,-0.9828,-0.9437,-0.8032]` with gate costs `3*4^n`. They are **synthetic** predicted readouts, not laboratory measurements. Added six `test_alexander_horned_C3_gauge_simulator.py` tests for C3 factors, commutator compatibility, gauge conjugacy invariance, Wilson orientation limitation and reproducibility; equivalent local test suite PASS 6/6.

**TRUE C3-UNITARY LAB ACTOR:** New `scripts/alexander_horned_C3_three_channel_SU2_actor.py` realizes `(2I)^3 rtimes C3` faithfully on THREE complex SU2 spin doublets, so `(2I)^3 rtimes C3 -> U(6)` by 2x2 quaternion matrices and C3 block permutation. It carries the selected cube as `diag(-I2,I2,I2)`, which disappears in A5 quotient. Independent equivalent local test PASS all 120 SU2 matrices, 300 products and sampled actor associativity. This complements the earlier minimal GL4(F7)/full GL12(F7) arithmetic actors but is more experimentally actionable.

**TRUE PHYSICAL BRIDGE, NOT AUTOMATIC SPIN CURVATURE:** a homomorphism `rho:pi1(E)->2I->SU2` supplies an AUXILIARY flat SU2 local system `(E_tilde x SU2)/pi1(E)`, by standard flat-bundle/holonomy reconstruction (Goldman-Millson 1988; standard Riemann–Hilbert). This proves mathematical existence of a specified flat nonabelian connection on the ideal wild exterior, but NOT a physically realized connection or an effect of the Euclidean Levi-Civita spin connection. Wilson trace alone is invariant under conjugation and cannot distinguish q from q^-1; additional matrix tomography is gauge-frame-dependent. A graph circuit has its OWN finite free-group topology and must not be advertised as a measurement of the infinite horned complement.

**PHASE GATES NOW:** (0) source/provenance — done; (1) abstract free group/C3/2I/spin — mathematical and finite done; (2) geometric existence — classical paper-level gluing proof supplied, entire infinite ambient map code still open; (3) geometric van Kampen — explicit cut atlas complete, standard source collar/round-star homeomorphism invoked rather than kernel-certified; (4) runnable finite synthetic gauge emulator — DONE / locally executed; (5) full three-channel C3 complex actor — DONE / finite locally verified; (6) physical apparatus/actual gauge measurement — NOT DONE; (7) specified PDE spectral experiment — NOT DONE. No Agda or CI work by user request. Full technical protocol `Docs/topology/AlexanderHornedC3GaugeSimulatorExperimentProtocol20261025.md`.
