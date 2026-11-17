# YM.REAL root-free rational S3 maximum cut — 17 November 2026

## Source and trust

This round analyzes and USES the existing original rational SU2 source,
rather than assuming unavailable Bishop square roots or a classical-pi
period. New source:
- YMClayRationalS3StereographicNodeExact.agda (pure rational norm algebra);
- YMClayRationalS3StereographicConcreteExact.agda (proved positive
  denominator, actual rational reciprocal, real original quaternion);
- YMClayRationalS3PositiveWeightedNodesExact.agda (finite original
  norm-one nodes, proved positive rational area weights, positive
  nonempty total, normalized list mass exactly one, and same-object
  original-rational-to-Bishop SU2 unitary consumer);
- check_ym_s3_stereographic_rational_20261117.py (1123 exact assertions);
- check_ym_s3_stereographic_invariance_20261117.py
  (1356 exact identities);
- check_ym_s3_exact_rational_orbit_designs_20261117.py
  (4840 exact rational assertions, complete degrees 7/9/11/13).

The constructed node and finite weighted-list sources are NOT a completed
continuous Bishop Haar or Agda kernel receipt. Existing non-safe rational
positivity/reciprocal owners remain isolated in the candidate regression;
only the pure safe norm algebra goes to the golden TOE import graph.

## 1. Actual rational S3 nodes, no roots, no pi

For t=(x,y,z) in Q³, let d=1+x²+y²+z² and

  phi(t)=((1-x²-y²-z²)/d, 2x/d, 2y/d, 2z/d).

The exact identity

  (1-r²)²+4r²=(1+r²)²

with r²=x²+y²+z² establishes phi(t) in the ORIGINAL
BalabanSU2RationalWilsonLargeFieldGapExact.RationalUnitQuaternion.
The denominator is strictly positive from nonnegative rational
squares, and its inverse is the pre-existing proved rational reciprocal,
not an assumed norm-one field.

Every rational S³ point except (-1,0,0,0) is of this form:
t=(q1,q2,q3)/(1+q0). The omitted south pole is already an obvious
literal rational original unit quaternion. Thus the constructed
rational nodes are dense in S³, and signed permutations of rational
unit quaternions also remain rational unit quaternions.

Exact chord identity:

  ||phi(t)-phi(u)||²
     = 4 ||t-u||²/[(1+||t||²)(1+||u||²)].

The pullback of the round metric is
4/(1+||t||²)² times the 3D identity; the area density is

  J(t) = 8/(1+||t||²)³.

It is strictly positive and rational for every rational t. Global
factor 8 is irrelevant to normalized finite rational weights.

## 2. Completely rational, positive, finite probability approximants

For any positive rational R and integer N>0, put h=2R/N,
take the N³ midpoint triples in [-R,R]³, evaluate phi at each
triple and assign raw rational weights h³ J(t). Every weight is
strictly positive and every node lies EXACTLY on S³. Normalize by
their positive rational sum. No square roots, analytic special
functions, implicit roots, π or floating-point coordinates enter.

The first finite checks include N=2,4,6,6 on cubes R=1,1,2,3:
each normalized weight sum is exactly 1; all q_i² unit equations
are exact; reflected odd spatial moments cancel; coordinate
permutation symmetries hold. The corresponding root-free
S3 checker passed 1123 exact symbolic/Fraction assertions.

## 3. Root-free constructive Cauchy estimate

Let |f|<=B and assume f is L-Lipschitz in the ordinary Euclidean
chord on S³. Then f(phi(t)) is 2L-Lipschitz, because the exact
chord formula bounds ||phi(t)-phi(u)|| <= 2||t-u||.

For J(t)=8/(1+||t||²)³:
  0<J<=8, ||grad J||<=48,
  Lip(J f(phi)) <=48B+16L.

The total area mass I0 of J over R³ is >1: on the unit cube
[-1/2,1/2]³, J>=512/343>1. The tail outside [-R,R]³ obeys the
elementary, pi-free product estimate

  ∫_{outside cube} J <= 768/R     (R>=1),

using J<=8/prod_i(1+t_i²),
∫R (1+t²)^-1 dt <=4 and
∫|t|>=R (1+t²)^-1 dt <=2/R.
These integral upper bounds follow by splitting into |t|<=1 and
|t|>1 and comparing with t^-2; there is no arctan/pi evaluation.

The cube midpoint Riemann error is <=8R³ h times the Lipschitz
constant, because a midpoint is at Euclidean distance <=h from
each point of its cell. Consequently the full mass error is

  e0 = 768/R+384 R³ h,

and the unnormalized f-integral error is bounded by

  ef = 768B/R + 8R³ h (48B+16L).

Provided e0<1/2, finite normalization remains positive and the
normalized discrepancy from the limit is at most

  2(ef+B e0).

Choose an integer C=ceil(1+B+L),
  R_k=2^(k+16)*C,
  h_k=R_k^-5.

Then for all nonnegative integers k and all rational B,L>=0,

  e0(k)<1/2,
  2(ef(k)+B e0(k))<=2^(-k-3).

This is a genuinely explicit Cauchy schedule. If Q_k(f) denotes the
normalized rational-node weighted sum of the Bishop-valued samples
f(phi(t)), for j>=k,

  |Q_j(f)-Q_k(f)|<=2^(-j-3)+2^(-k-3)<=2^(-k-2).

The actual vendor Sequence._isCauchy requests precision 1/K for
arbitrary positive natural K; choosing e.g. k>=4K is more than enough.
The native Agda proof must transport the rational tail/midpoint
estimates and that threshold to Bishop. The full finite sum at k=0
is astronomically large; this is a proof-producing formula rather
than a practical numerical quadrature algorithm.

For general bounded uniformly continuous f use its supplied
effective modulus to bound f∘phi on the compact cube; fixed
Lipschitz constants are not necessary. Positivity, normalization
and setoid contractivity of the resulting limit follow from its
positive normalized finite sums and the Bishop Cauchy limit.

## 4. All-degree sphere moments, without an assumed Haar functional

For i=1,2,3 define rational vector fields on R³

  V_i(t)=((1-||t||²)/2)e_i+t_i t.

Exact symbolic polynomial reduction proves

  div(J V_i)=0,
  V_i · grad(phi_0)=-phi_i,
  V_i · grad(phi_i)=phi_0,
  V_i · grad(phi_j)=0 for j!=0,i.

For any polynomial P restricted to S³, integration by parts over
[-R,R]³ gives ∫ J(V_i·grad(P∘phi))=0 as R→∞.
The boundary term vanishes because J=O(R^-6) on a cube face,
V_i=O(R²) and face area=O(R²). This yields invariance under
rotations in every (0,i) plane, whose commutators generate
so(4); direct t_i reflections give remaining odd-coordinate
cancellation. The normalized integral is SO(4) invariant.

Apply the generator L_ij=q_i∂_j-q_j∂_i and q0²+q1²+q2²+q3²=1
to derive the universal moment recurrence, for a_i>=1 and
k=sum_i a_i:

  H(q_0^(2a0)...q_i^(2ai)...q_3^(2a3))
    = (2ai-1)/[2(k+1)]
        H(q_0^(2a0)...q_i^(2ai-2)...q_3^(2a3)).

With H(1)=1 and odd-moment cancellation this proves

  H(prod_i q_i^(e_i)) =
    0 if some e_i odd,
    prod_i(1/2)_(e_i/2)/(2)_(sum_i e_i/2) otherwise.

This *derives* the original all-degree Pochhammer functional from
positive rational stereographic area; it is not an assumed Haar
integral. check_ym_s3_stereographic_invariance_20261117.py verifies
the exact divergence and rotation equations and 1356 resulting
algebraic instances. The full integration-by-parts/change-of-variable
proof is mathematically stated here, NOT yet an Agda kernel proof.

## 5. Even stronger: exact rational positive cubatures

The new standalone certificate verifies full S³ moment equality
using ONLY positive RATIONAL weights on RATIONAL unit quaternions,
without an algebraic root or trig value:

  degree  7: 3 signed-permutation orbit families; 120 nodes;  330/330
  degree  9: 5 orbit families; 360 nodes;  715/715
  degree 11: 6 orbit families; 696 nodes; 1365/1365
  degree 13: 9 orbit families; 1000 nodes; 2380/2380

All signed/permutation orbit nodes have exact rational unit norm;
all orbit masses are strictly positive and exactly sum to one;
every monomial in each complete basis is checked against the
all-degree Pochhammer formula. Total 4840 exact rational
certificate assertions. Candidate selection was assisted by a
linear optimizer; the COMMITTED certificate is static and requires
no optimizer, floats or external root-finding.

The simple degree-7 certificate has orbit representatives
  (1,0,0,0), (1/2,1/2,1/2,1/2),
  (-1/3,2/3,2/3,0)
with respective total positive orbit masses
  167/960, 1/15, 243/320.

**All-degree exact rational existence theorem:** For a fixed degree d,
consider the finite-dimensional space V_d of restrictions of
polynomials to S³. The preceding positive full-support rational
stereographic integral gives a rational moment vector H_d which lies
in the RELATIVE INTERIOR of the convex hull of all sphere evaluation
vectors: if a nonzero nonnegative polynomial had mean zero, its
strictly positive open subset would contradict the positive density.
Rational stereographic points are dense on S³, so H_d also lies in
the convex hull of RATIONAL evaluation vectors (relative interiors
of a convex set and its closure coincide). A finite subset yields a
rational linear feasibility system, and a feasible rational system
admits a rational nonnegative solution. Discard zero weights.
Therefore a positive exact rational cubature exists for every d,
and exhaustive enumeration of rational nodes/weights with exact
moment tests terminates at every requested d. Its computational
complexity may be very large.

This is a mathematical argument using finite-dimensional convex
separation/full support, NOT an inhabited constructive Agda termination
or universal explicit bounded search theorem. The native proof
must formalize an effective convex-moment interior certificate or a
validated witness generator for each requested d. The explicit
low-degree rational witnesses remove the actual root/π dependency
in those cases immediately.

## 6. Original Wilson and RG boundaries

The rational nodes inhabit the same original
BalabanSU2RationalWilsonLargeFieldGapExact.RationalUnitQuaternion,
and the existing rational-to-Bishop source transports them to the
Bishop 2×2 matrix/determinant/unitarity candidate. Thus no
second sphere or independent group is required. The original
four-dimensional positive-bond/plaquette Wilson polynomial source
can integrate any finite polynomial using these exact rational
cubatures whenever their degree is sufficient.

For the full Wilson exponential, the Taylor upper/lower brackets
and factorial tail supply a finite-cutoff partition limit once
all-degree cubature/equivalence is inhabited. Existing exact
all-cutoff moment bounds stand. The naive fixed-beta L2→L1 link
selection is PROVED NOT projectively consistent. A genuine RG
cylinder theorem must use an explicit blocking map and induced
effective action, not a false raw-link restriction.

## Honest kernel ledger

All five named original YM.REAL formal obligations are STILL OPEN
at the pinned Agda trust level. This round DOES close the root/π
DEPENDENCY in the explicit rational finite-node construction and
supplies exact positive cubature witnesses through degree 13, plus
a root-free mathematical all-degree completion route.

No Agda compiler, pinned Nix replay, or transitive --safe check was
available in this environment. Do not promote mathematical/verified
symbolic results to Agda kernel acceptance or Clay Yang-Mills.


### 2026-11-17 continuation: compressed degree-13 source certificate and new degree-15 rational Wilson endpoint

**New exact mathematical/algorithmic result:** signed-coordinate and
permutation invariance reduces every polynomial of degree <=13 on S3
to nine elementary symmetric constraints in yi=qi²:
1, e2, e3, e4, e2², e2e3, e2³, e3², e2e4, using e1=1.
The independent exact SymPy checker
scripts/check_ym_s3_degree13_nine_invariants_20261117.py
checks all nine weighted rational moments of the nine existing
rational-orbit representatives and all symmetrized monomial orbits
through y-degree 6. The full 2380-monomial checker remains an
independent control. The new safe-source Agda
YMClayRationalS3DegreeThirteenInvariantCertificateExact
uses nine ACTUAL original RationalUnitQuaternion constructors and
rational masses, with nine closed invariant arithmetic equations.
This is NOT an Agda theorem formalizing the Reynolds
sign/permutation symmetrization and basis spanning step.
No pinned Agda kernel was available.

**New degree-15 positive rational cubature:** a rational linear LP
search over 20 low-denominator rational signed/permutation orbits
found eleven positive orbit masses. They were reconstructed with an
exact rational linear solve; the static certificate itself uses no
LP, floats, roots, angles, pi, or square roots.
scripts/check_ym_s3_exact_rational_orbit_degree15_20261117.py
independently verified **3876/3876** full monomials, strict positive
masses, exact unit norm and mass-one normalization.
The fully expanded signed/permutation cubature has **1464 nodes**.
The first 11 invariant constraints in yi of weighted degree <=7
are 1, e2, e3, e4, e2², e2e3, e3², e2e4, e2³,
e3e4, e2²e3. Numerical discovery is not proof;
the committed rational certificate is the exact proof witness.

**Concrete original Wilson finite-volume consequence.**
A positive exact degree-15 rule in EACH original link integrates
the actual polynomial Taylor series through degree 15 at all
original periodic sides L>=2, since each elementary plaquette
contains any one original positive bond at most once. The L=1
commutator reuses each of two bonds twice, so degree 15
integrates through Taylor order 7. In both cases the alternating
Taylor bounds are genuinely valid for ALL beta>=0.
At beta=1/(96 L⁴), the guaranteed interval width is
1/10569646080 at L=1 (T7/T6), and
1/46009701534740225458176000 at L>=2 (T15/T14).
scripts/check_ym_original_wilson_rational_degree15_taylor_budget_20261117.py
checks exact original edge incidence through L=4 and these
factorial interval bounds. **The high-order endpoint integrals
have not been expanded or evaluated**; the interval-width result
does not claim an actual numerical partition value.

**Trust:** these exact rational cubature witnesses substantially
advance the physical polynomial cylinder, but do not inhabit
the Bishop all-degree cubature/Cauchy/continuous-Haar source,
the original full SUN matrix equivalence, or the selected RG
disintegration bridge. No transitive Agda acceptance receipt,
no mass-gap/continuum claim. Maintain YM.REAL OPEN.


### 17 November 2026 — next implementation: degree-15 11-invariant source weld

New finite original-SU2 source proof candidates, committed to PR #1444:

- DASHI/Physics/YangMills/YMClayRationalS3DegreeFifteenInvariantCertificateExact.agda
  reuses the original rational quaternion constructor and the prior
  degree-13 invariant functions. Its 11 rational representatives
  have norm-one closed polynomial witnesses, and it writes the exact
  11 invariant moment equations as definitional rational arithmetic.
  Tagged --safe but no pinned Agda/CI kernel result exists.
- scripts/check_ym_s3_degree15_eleven_invariants_20261117.py
  checks each invariant by independent exact methods: evaluate positive
  rational orbit masses and expand into Pochhammer coordinate moments.
  It verifies all 38 distinct signed-permutation orbit-sum monomials of
  squared-coordinate degree <=7 reduce (using e1=1 on S3) into
  the explicitly listed 11-dimensional invariant span.
  Locally 11/11 moments and 38/38 orbit classes passed.
- The independent scripts/check_ym_s3_exact_rational_orbit_degree15_20261117.py
  passes 3876/3876 monomials on the 1464-node rational rule.
  The original Wilson T15/T7 degree budget remains a bound, not
  evaluated high-order Taylor partition coefficients.

Exact source moment targets:
1=1; e2=1/4; e3=1/48; e4=1/1920;
e2^2=11/160; e2*e3=1/160; e3^2=3/4480;
e2*e4=3/17920; e2^3=89/4480;
e3*e4=3/143360; e2^2*e3=69/35840.

NEXT KERNEL CUT: formalize in Agda the actual signed/permutation orbit
averaging and its action on every coordinate monomial through degree
15, then the invariant-basis reduction and the uniform positive
finite orbit weights. A sum over one representative per orbit is
NOT the actual full signed-permutation orbit measure.

ORIGINAL WILSON/RG: reuse existing
YMClayFiniteRGExistingPushPullReopeningWeldExact and
BalabanFiniteProbabilityPartitionDisintegrationExact, rather than
rebuilding finite disintegration. Instantiate them on the actual
rational-design original SU2 link product Gibbs measure and the
original selected block map, verify positive selected coarse fibres
or remove zero-mass fibres, then bridge to the actual Bishop limit
and original SUN matrix carrier. The RealAnalysisAxioms.ℝ legacy
carrier remains different from Bishop Real.ℝ.

Remaining YM.REAL formal obligations OPEN: universal constructive
positive rational design search termination, native Bishop
multivariate order/Cauchy proof, completed actual SU2 Haar
bilateral invariance, pinned original SU(N) carrier mapping,
original Wilson finite product and selected physical RG transfer.
No pinned Agda kernel acceptance is claimed.
