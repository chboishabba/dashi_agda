# C3 semisimplicity max-cut: same R3/Spin action over Q, F2, F3, F5, F7

Date: 2026-10-24. Existing PR #1244. Attribution / source object audit.

## Corrected research framing

The user did NOT expect C3 alone to certify a global non-split
Spin obstruction. The already paid exact owner
`AlexanderHornedC3SpinLiftSplitExact.agda` explicitly proves
a coherent order-three signed lift; its path-selected
section has a concrete 2-cocycle which is a coboundary.
That is a POSITIVE existence/compatibility result.
Do not reframe H^2(C3,C2)=0 as a setback or a demand that
C3 somehow produce a non-split extension.

The mathematical reason is classical: Aut(C2)=1, so the
C3-action on the C2 coefficient group is trivial, and
periodic cyclic cohomology yields
    H^2(C3,C2) = C2/(3 C2) = 0.
The general splitting consequence also follows from
Schur-Zassenhaus for coprime orders 2 and 3.
Source: Dietrich Burde, Group Cohomology lecture notes,
https://homepage.univie.ac.at/Dietrich.Burde/papers/burde_16_coho_course.pdf
The older repo proves its PARTICULAR cocycle explicitly;
it does not internally build a general group cohomology
derived-functor library. Keep these proof levels separate.

The non-split 2I->A5 cover is useful for a DIFFERENT
question, spin-sign sensitivity and global finite-group
projectivization, not because C3 'failed'.

## Prior repository discovery — no rebuilding

1. `Core.FiniteC3OrbitStabilizerExact`: genuine order-3 group.
2. `AlexanderHornedC3SpinLiftSplitExact`: six-element group
   `C3 x C2`, strict order-three section, cocycle/coboundary,
   uniqueness for signed lift.
3. `AlexanderHornedC3SpinLiftSteelman20261024.md`:
   Pauli-matrix Dirac covariance and finite VOA module
   consumers already scoped and finite-audited.
4. `DASHI/Moonshine/C3FourierConjugationExact.agda` and
   `C3CyclotomicRealDescentExact.agda`: symbolic Fourier rows
   and 1 fixed real axis + 2D rational conjugate sector.
5. `DASHI/Analysis/NormalizedFibreAveragingExact.agda`:
   proof-bearing rational Reynolds-style fibre projection
   for a TWO-point fibre, now reused as proof pattern
   for an ACTUAL threefold orbit.
6. `DASHI/Wikimedia/IbrahimMonster3BWholeCharacterIsotypicBypassExact.agda`:
   pinned mathlib Maschke, FDRep character and isotypic
   donor sources. Its own Monster isotypic reconstruction
   bridge is explicitly still conditional.
7. `DASHI/Physics/Foundations/R3HodgeCrossExact.agda`:
   actual R3 wedge, Hodge star, cross product, and
   su2 Lie-bracket normalization [u,v]=2(u x v).
   These are now matched to our literal xyz->zxy
   C3 rotation via exact polynomial equivariance.
8. `DASHI/Foundations/BinaryPolyhedralMcKayDimensionExact.agda`:
   E6/E7/E8 McKay *dimension* skeleton, not a
   physical exceptional E_n Lie action or E_n operad.
   These are different mathematical meanings of 'E_n'.
9. `DASHI/Physics/QFT/SpinorRepresentationReceipt.agda`:
   F2^2 spinor / F2 Clifford label only, with
   -1 = +1 sign collapse. It itself says no derived
   fermionic statistics. This is why F5/F7 are
   preferable for sign-sensitive semisimplicity.

## Same C3 action, distinct coefficient fields

Use literally the SAME integral 2x2 companion matrix
    A = [[0,-1],[1,-1]].
It obeys A^2+A+I=0 and A^3=I over Z, and hence
over any field F. Its characteristic polynomial is
    f(t)=t^2+t+1.

Field      C3 representation on F^2
-----      ---------------------------
Q          irreducible rational 2D cyclotomic, semisimple
F2         irreducible 2D, semisimple by Maschke,
           BUT -1=+1 so the central spin sign is erased
F3         (t-1)^2; a nontrivial 2x2 unipotent Jordan
           block; one-dimensional fixed line, NO
           invariant complementary line, nonsemisimple
F5         f(t) irreducible, Maschke applies,
           nontrivial 2D irreducible; -1 != +1
F7         f(t)=(t-2)(t-4), distinct eigenvalues;
           direct sum of two 1D character lines,
           with explicit complementary projectors
Q3         char ZERO, so Maschke applies;
           no primitive zeta3 scalar in Q3, but
           two-dimensional cyclotomic representation
           is irreducible; its REDUCTION mod3 is not.

Note the logical nuance: Maschke states ALL
representations are semisimple if char does not divide
|C3|. If char=3, SOME modules (e.g. trivial 1D) can
still be semisimple. It is only the universal guarantee
that fails. The literal A is a genuine nonsplit example.

At p=3, N=A-I is NONZERO yet N²=0. This proves
the two-dimensional Jordan block is not diagonalizable.
Exact enumeration of ALL four lines in F3² shows
only the fixed line is C3-stable; hence the fixed
line has NO C3-invariant complementary line.

At p=7 the two rank-one spectral idempotents are
    E2 = (A-4I)/(2-4),
    E4 = (A-2I)/(4-2),
and satisfy E2²=E2, E4²=E4, E2E4=0,
E2+E4=I, AE2=2E2, AE4=4E4.
Over F5, f has no root and A is irreducible.

In all p != 2, the scalar -I differs from +I.
For the path-signed lift -A, (-A)^3=-I, while
the coherent lift A satisfies A³=I.
This is an exact algebraic SIGN observation,
not a continuous path theory over finite fields.

## Same actual three-dimensional horn rotation: Maschke projector

For R(x,y,z)=(z,x,y), define over Q
    P=(I+R+R²)/3,
    Q=I-P.
Then
    P²=P; Q²=Q; PQ=QP=0; P+Q=I;
    PR=RP=P; QR=RQ.
Thus Q³ splits into the C3-fixed DIAGONAL LINE
and the sum-zero transverse 2-plane, an actual
direct-sum realization of the old 1+2 cyclotomic
sector decomposition.

NEW proof owner:
`DASHI/Mathematics/Topology/AlexanderHornedC3MaschkeReynoldsExact.agda`,
which imports the ACTUAL Horn R3.rotateXYZ, and
`NormalizedFibreAveragingExact`, `C3CyclotomicRealDescentExact`,
`C3FourierConjugationExact`. Algebraic equalities are
source-written using existing rational ring-solver proof terms.
No Agda exact-head kernel receipt has yet returned.

Finite field checks apply precisely this same R:
- F2, F5, F7 have rank-one P and rank-two Q,
  complementary and equivariant.
- F3 cannot form 1/3; S=I+R+R² is nonzero
  but S²=0, so it is NOT a projector.

THIS is the exact controlled Maschke / non-Maschke
contrast requested, not a new C3 group theory framework.

## R3/Hodge/Spin E_n cross-pollination — mathematical not numerical

The new
`AlexanderHornedC3R3HodgeEquivarianceExact.agda`
reuses `R3HodgeCrossExact` to show the literal
R(x,y,z)=(z,x,y) rotates the bivector components as
    (xy,yz,zx) -> (zx,xy,yz),
and preserves the wedge, cross and Hodge-star maps.
Thus `R cross(u,v) = cross(Ru,Rv)`,
`R *(omega) = *(R omega)` after accounting
for vector versus bivector carriers.

These are algebraic same-map intertwiners over the
existing R3 real scalar interface, not a new proof of
a smooth spin connection or metric-coupled Dirac operator.
The rational quaternion carrier and axiomatic real carrier
must still be connected by a coefficient map.
The E6/E7/E8 McKay skeleton is useful for spin/
binary-polyhedral group restrictions, but its dimensions
alone do not pay this map. No E_n operad claim made.

## Crucial fixed-axis versus free-orbit distinction

For the genuine order-three two-component spin lift,
the characteristic polynomial of its spin matrix is
t²+t+1. Therefore at any fixed spatial point:
- over Q,C,Q3,F5,F7 the spinor has NO +1
  eigenvector in this 2D representation;
- after reduction to F3 it HAS a nonzero fixed line,
  due to modular unipotence.

But for three DIFFERENT points forming a C3-free
spatial orbit, with 2 spin components at each point,
the six-dimensional induced representation has
a TWO-dimensional fixed space OVER F3 AS WELL
AS over F5 and F7. This does NOT mean the F3
representation is semisimple; its invariant summand
need not admit a stable complement.

All these invariants are representation-theoretic
fixed vectors. They are NOT solutions of D psi=0,
let alone physical zero-energy Dirac eigenmodes.
A self-adjoint Dirac realization, boundary/domain,
continuum limit, normalization and coupled-field
data remain separate geometric and analytic gates.

The reduction from Q3 to F3 cannot by itself promote
a new characteristic-3 fixed vector into a Q3 (or
complex) eigenvector. Q3 has characteristic zero
even though its residue field has characteristic 3.

## Verification ledger and next max-cut

New finite regression:
`scripts/alexander_horned_c3_maschke_prime_comparison.py`
contains exact Fraction matrices, exhaustive F3
stable-line classification, F5/F7 spectral projectors,
R3 Reynolds splitting over Q/F2/F5/F7, and the
three-site times two-spin induced action over F3/F5/F7.
An independent local Python audit PASSED every stated
finite identity (with additional p=11 sanity test).

New finite F3 proof owner:
`AlexanderHornedC3ModularJordanF3Exact.agda`
defines literal field-3 addition/negation and same A,
proves A³=I, N²=0, N != 0, a nonzero fixed vector,
and no 1/3 scalar by nine/three finite cases.
This is not a claim that ALL F3 representations
are nonsemisimple.

P0 (PAID): correct C3 split spin and cocycle status;
    this was always an intended compatible action.
P0 (PAID FINITELY): same C3 field comparison,
    char3 nilpotent versus char5/7 Maschke.
P1: actual exact-head Agda/Lean kernel receipts,
    and full native F5/F7 field instance if needed.
P2: demonstrate R(B)=B for an actually embedded
    three-root horned ball B with collared covers.
P3: domain/operator/metric and spin-structure
    gluing for any spectral or global physical claim.
P4: optional existing E6/E7/E8 binary polyhedral
    representation restriction, only on selected
    same-object source group/axis; do not overindex
    on order/dimension coincidences.

Attribution firewall: Maschke classical; Milne/Serre
expositions; project-specific exact finite spin source
from prior repository; new modules and tests are
source-written until a kernel receipt verifies them.

External sources:
- Maschke: https://jmilne.org/math/CourseNotes/GTe6.pdf
- Group-representation text, concrete C3 invariant
  projector: https://www.maths.dur.ac.uk/users/jack.g.shotton/repthy/sec-finite-groups.html
- Modular indecomposable cyclic group representations:
  https://doi.org/10.1016/j.jpaa.2005.07.003
- Burde cyclic-group cohomology and coprime splitting:
  https://homepage.univie.ac.at/Dietrich.Burde/papers/burde_16_coho_course.pdf
- Binary icosahedral historical group source:
  https://math.ucr.edu/home/baez/icosidodecahedron/23.html


## 2026-10-24 decisive follow-on: SAME quaternion spin matrix and full F7 actor

**Stronger actual same-object representation owner**
`DASHI/Mathematics/Topology/AlexanderHornedC3SpinCyclotomicIntertwinerExact.agda`
reuses the LITERAL Cayley-Dickson rational Gaussian-complex
and rational quaternion carriers. Let q=(1+i+j+k)/2,
V=U(-q) in the standard Gaussian 2x2 quaternion realization,
and A=[[0,-1],[1,-1]]. The explicit invertible change-of-basis
matrix and its inverse are

    T    = [[1, -(1+i)/2], [0, (1-i)/2]],
    T^-1 = [[1, i],       [0, 1+i]].

The new owner proves V*T = T*A and both inverse laws
by componentwise rational polynomial identities.
An independent local exact Gaussian-rational probe
also passed modulo 3, 5 and 7 (over the corresponding
Gaussian quotient algebras). Since det(T)=(1-i)/2
and its norm is 1/2, T remains invertible modulo
every odd prime. This **pays** the former same-carrier
gap between the actual Horn coherent quaternion rotor
and the cyclotomic companion field-comparison matrix
at odd characteristic. p=2 is deliberately excluded.
Script:
`scripts/alexander_horned_c3_spin_cyclotomic_intertwiner_audit.py`.

**Full finite-group Maschke break** is stronger than
the C3-only character calculation:

    Gprojective=A5^3 rtimes C3, |Gprojective|=648000
    Gspin=2I^3 rtimes C3,      |Gspin|=5184000.

Both orders are 3 modulo 7. Therefore **Maschke applies
to every linear representation of BOTH full actors over F7**.
In characteristic 5, C3 alone is semisimple, but the
full A5 and 2I actors are modular. In characteristic
2 the central spin sign collapses. Characteristic 7
is thus the smallest prime simultaneously avoiding
2,3,5, preserving +/- spin, and allowing full finite
spin/projective-actor semisimplicity.

NEW exact arithmetic owner
`AlexanderHornedC3F7FullActorMaschkeExact.agda`
proves both group orders and their division-with-remainder
formulas, the 180/360 coordinate double-fibre identity
and its rational normalized mean coefficient.
Maschke's theorem itself is attributed to the pre-existing
pinned mathlib/classical source; not falsely reconstructed
as a new Agda theorem.

**Same finite module / projector diagram:**
with pi:OmegaS=C3x2I -> OmegaA=C3xA5 (2:1),
the uniform average on either function space over F7
is the projection to constant invariant functions.
Each finite group acts transitively on its coordinate set.
Since 180 mod7=5 and 360 mod7=3,

    180^-1 = 3 mod7, 360^-1 = 5 mod7,
    2 * 360^-1 = 180^-1 mod7.

Therefore for EVERY f on OmegaA,

    P_S(pi^* f) = pi^* (P_A f).

The full finite SL2(F5) quotient, five Q8 subgroups,
360->180 fibre counts, normalized averages and
group translations were checked independently with
exact finite arithmetic:
`scripts/alexander_horned_c3_f7_full_actor_reynolds.py`.
This is a genuine equivariant, mode-compatible finite
algebraic result, not a claim that the actual selected
Monster VOA or physical Dirac spectrum is realized.

Proof levels: these three new Agda modules are SOURCE
WRITTEN, not exact-head kernel checked. The scripts
were independently reproduced locally and committed.
Geometric horned R(B)=B, analytic Dirac domains,
and 3-copy exterior pi1 are still independent gates.
