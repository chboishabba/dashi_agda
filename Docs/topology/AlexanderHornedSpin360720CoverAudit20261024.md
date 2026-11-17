# 360-degree SO(3) rotation versus 720-degree Spin(3) return

Date: 2026-10-24. Maintainer: Alexander horned C3 PR #1244.

## Exact mathematical statement

Spin(3) = SU(2) = unit quaternions, and the two-to-one
continuous group cover is

    1 -> {+1,-1} -> Spin(3) -> SO(3) -> 1.

The covering map acts on pure imaginary quaternions by
    rho(q)(v)=q v q^{-1}.
Its two-element central kernel is {+1,-1}. The continuous
path of rotations through angle theta, started at the
identity, has lift

    q(theta)=cos(theta/2)+n sin(theta/2).

Thus 0deg: +1, 360deg (2pi): -1, 720deg (4pi): +1.
Spatial vectors are unchanged at both 360 and 720.
A 360deg LOOP in SO(3) is not nullhomotopic; its doubled
720deg loop is nullhomotopic: pi1(SO3)=Z/2,
pi1(SU2)=0. Being the identity as a GROUP ELEMENT
after 360deg is not being contractible as a LOOP OF GROUP
ELEMENTS (the Dirac belt trick distinguishes them).

A spin-j irrep of SU2 responds to its central -1 by
    (-1)^(2j).
For half-integer j it changes sign under 360deg,
returning at 720deg, and does not descend to SO3.
For integer j it is invariant under 360deg and does
descend to SO3. A global sign on an isolated quantum
state ray does not change its probabilities; its relative
sign compared to another path can matter in interference.

SOURCES:
* University of Alberta SU(2) notes,
  https://sites.ualberta.ca/~vbouchar/MAPH464/section-su2.html,
  explicit U(theta+2pi)=-U(theta).
* University of Colorado Boulder, Dirac string trick:
  https://physicslabs.colorado.edu/demos/modern-physics/atomic-physics/electron-properties/dirac-string-trick/
* John Baez, rolling spinor and quaternion double cover:
  https://golem.ph.utexas.edu/category/2013/06/g2_and_the_rolling_ball.html.
Primary conventional sources: Cartan spin groups, Hamilton
quaternions; these references are EXPLANATIONS of their
standard mathematical results, not original invention.

## Precise prior work discovered in THIS repository

1. `DASHI/Foundations/SU2SO3IrrepDimensionExact.agda`:
   exact even-highest-weight SO3 descent and the
   spin-half highest-weight one non-descent theorem.
   This is the exact type-theoretic spin/rotation
   REPRESENTATION obstruction already in the repo.

2. `DASHI/Algebra/FiniteQuaternionDoubleCover.agda`:
   explicit multiplication of Q8 and two-to-one quotient
   Q8->V4, with exact central kernel and two-point
   fibres. THIS IS A FINITE SUBGROUP MODEL, not a
   theorem about continuous SU2->SO3.

3. `DASHI/Mathematics/Topology/AlexanderHornedQuaternionC3SpinExact.agda`:
   literal rational quaternion q=(1+i+j+k)/2,
   q^3=-1 and (-q)^3=+1, two lifts of the SAME
   120deg spatial rotation (x,y,z)->(z,x,y).
   The existing Hopf/Q8/Cayley-Dickson sources supply
   norm, product and unit action checks.

4. `DASHI/Algebra/CliffordSpinLift.agda` and
   `DASHI/Geometry/Clifford/SpinFromSignature.agda`:
   Clifford/Spin derivation INTERFACES. Some
   `Bool=true` statuses are not term-level
   constructive kernel/cover proofs. Do not use these
   booleans as evidence of a continuous spin theorem.

5. `DASHI/Algebra/ContinuousSpin31LorentzCover.agda`:
   explicitly typed *conditional* continuous cover
   for Spin(3,1) -> SO^+(3,1), **different target**.
   Its records require concrete smooth/topological
   data, so merely seeing the record does not close
   `Spin(3)->SO(3)` covering-space topology.

6. `DASHI/Physics/SpinAssumptions.agda`:
   the default record inhabits trivial singleton
   carriers and stores `surj : ⊤`, `twoTo1 : ⊤`.
   It is a data-level placeholder, NOT a strict
   mathematical double-cover proof.

## New exact-horned 360/720 connection

`DASHI/Mathematics/Topology/AlexanderHornedSpin360720Exact.agda`
directly REUSES the finite Q8->V4 theorem and proves
by literal group multiplication:
    rho(+1)=rho(-1)=spatial_identity;
    -1 != +1;
    (-1)*(-1)=+1;
    i*i=-1 although rho(i)*rho(i)=identity;
    the spin-half highest weight cannot descend to SO3.

The same new module imports the previous actual
120deg horn rotor and proves its spatial C3 cube=identity,
its chosen Spin lift q^3=-1, and the other lift
(-q)^3=+1. These last are wrappers around the
existing earlier quaternion theorem, not new proofs
of the continuous Spin covering map.

`scripts/alexander_horned_spin_360_720_audit.py`
is a reproducible exact Fraction audit covering the
full Q8 finite quotient fibres and q rotor.
An independent exact arithmetic reproduction PASSED
for quaternion multiplication, 360 sign, 720 return,
the cycling of axes and the signed threefold lifts.
The committed script itself is wired into CI but
an executable CI receipt is still pending.

### Angular lift ordering subtlety

For an SO3 120deg rotation about the (1,1,1) axis,
q=(1+i+j+k)/2 is the endpoint of the path theta:0->120deg,
q^3=-1 is the endpoint after theta:0->360deg,
and q^6=+1 follows at 720deg.

The SAME SO3 120deg element has another lift -q.
Its cube is +1 because the chosen lift is not the
endpoint of the SAME identity-starting 0->120deg path.
This does not violate the 720deg return statement:
the path lift and an arbitrarily selected group lift
are DIFFERENT objects.

A sign-sensitive finite 2I->A5 quotient can register
this sign. It is not thereby a faithful representation
of the wild fundamental group; the abstract horned
source remains torsion-free and the selected 2I spin
image can have finite order.

### 360 dimension versus 360 degrees

The recently built functions on C3 x 2I have
3 * 120 = 360 COORDINATES. That number is a
VECTOR-SPACE DIMENSION, not an angular periodicity.
Its projective C3 x A5 predecessor has 180 coordinates
(3 * 60), again unrelated to degrees. Avoid spurious
180deg/360deg identifications from dimensional counts.

## Exact promotion boundaries

PROVEN classical theorem: continuous Spin3->SO3
cover, angle 2pi/4pi spinor laws.

EXACT PREVIOUS SOURCE: finite Q8->V4, SO3
descent by even SU2 highest weights.

NEW SOURCE-WRITTEN (not yet kernel check):
360/720 strict finite witness module.

FINITELY AUDITED locally: quaternion multiplication
and finite cover fibres.

STILL OPEN: Agda exact-head typecheck, constructing
actual continuous universal-cover/path-lift theorem
from topology libraries, tying any true geometric
horned exterior pi1 to abstract three-root colimit.

This document does not claim a 360deg torsion
element of pi1(exterior), physical Berry holonomy,
a quantum consciousness mechanism, or Monster
VOA identity.


## 2026-10-24 C3 steelman: strict spin action versus 720-degree angular path

See canonical attributions, exact data and proof-status ledger:
`Docs/topology/AlexanderHornedC3SpinLiftSteelman20261024.md`.

**P0 mathematical break:** restricting Spin3->SO3 to the
actual 120deg C3 subgroup gives a SPLIT central extension
`C6 ≅ C3×C2`, since `H²(C3,C2)=0`. The old rational
quaternion `q=(1+i+j+k)/2` (order 6, q³=-1) is the
identity-started +120deg PATH lift, NOT a homomorphic C3
generator. The same rotation's other lift `-q` has
order 3, giving a genuine spin-equivariant C3 action.
Neither lift changes the torsion-free source exterior G.

**Agda exact source:** `AlexanderHornedC3SpinLiftSplitExact.agda`
reuses EXISTING `FiniteC3OrbitStabilizerExact`, Q8 signs
and ambient horn C3. It constructs the six-element spin
preimage, a strict homomorphic C3 section, unique
order-three generator lift, a nonhomomorphic path-section,
and proves by all nine cases that the path's central
carry cocycle is an EXPLICIT coboundary.
No continuous covering-space Agda kernel certificate
has been created.

**A same-coordinate Dirac field consumer exists** on ANY
C3-invariant open subset E of R3:
`Tψ(x)=U(-q)ψ(R^-1 x)`,
`T³=1` and `DT=TD` on
compactly supported two-component spinors.
The Gaussian-rational `spin_dirac_probe.py` checked
all three Pauli/Dirac coefficient identities and
125 exact finite position/spinor samples.
This requires `R(E)=E` for the *actual* wild
embedding, not a completed fundamental-group theorem,
nor any spectral domain/self-adjointness statement.

**Fixed-axis and characteristic-3 discriminator:**
`tr(U(-q))=-1`, `det(U(-q)-I)=3`; fixed-axis
C3-invariant spinor values vanish in characteristic
zero. On each free 3-position orbit with two spin
components, the exact averaging projector
`P0=(I+T+T²)/3` is idempotent of rank 2.
The Q3 2D cyclotomic block has zero fixed dimension,
whereas reducing it modulo 3 yields a unipotent
representation with a 1D fixed subspace. This is
Maschke failure, not a new characteristic-zero zero
mode or Monster eigenspace. The existing C3Fourier/
C3CyclotomicRealDescent/3B projector owners are
literature/technique donors, NOT the same spinor operator.

**Spinor MODULE over SAME finite scalar VOA:**
`V=Fun(C3×A5,Q)` has 180 scalar sites;
`M=Fun(C3×A5,H_Q)` has 720 rational coordinates.
It admits a right-Q(i) spinor complex structure,
yielding 360 dimensions over Q(i), which is NOT
`Fun(C3×2I,Q)`, the distinct old 360-site spin
charge algebra. For `g=(a,k)`, spinor right pullback
is `r^k ψ(g.x)` with r=-q, and preserves scalar
pointwise vertex-module multiplication. The existing
finite semidirect actor is reused. The finite
`spin_voa_module_probe.py` checked 18 sampled
actors, 18x18 group pairs, 180 sites and sign
periodicity. No Monster-VOA module is identified.

**Full A5 global obstruction still non-split:**
`2I->A5` remains globally non-split even though
its restriction to any C3 subgroup splits. Hence
C3 alone is NOT a test of the global spin Schur
class. Continue using an actual 2I/A5 same-object
map for this, not an order-three phase analogy.

Independent local finite probes PASS, CI files updated,
but no successful exact-head Agda/Lean workflow
receipt returned. The geometric `R(B)=B` and
van Kampen identification remain open.
