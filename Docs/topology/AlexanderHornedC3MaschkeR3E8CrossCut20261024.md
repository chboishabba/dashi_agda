# Horned C3 semisimplicity: exact characteristic comparison, R3 spinor and McKay E_n reuse

Date: 2026-10-24, existing PR #1244. MAX-CUT means source audit,
separating the carrier types, and completing the highest-value
theorems before inventing fresh notations or status flags.

## Main correction: C3 splitting was never the target obstruction

Previously built, not an open failure:
- `DASHI/Mathematics/Topology/AlexanderHornedC3SpinLiftSplitExact.agda`
  implements the actual split restriction of Spin3->SO3 to C3,
  q^3=-1 versus (-q)^3=+1, the carry cocycle, its explicit
  trivializing cochain, uniqueness of its order-three lift.
- Existing actual full 2I->A5 quotient has a GLOBAL NONSPLIT
  twofold central extension. The C3 restriction splits,
  consistent with H^2(C3,C2)=0. This is not new negative progress.
- Source: standard group cohomology H^2(C_n,A)=A/nA
  for trivial A, plus Schur-Zassenhaus (coprime extension).
  This is not a statement about horned exterior pi1 torsion.

## Relevant prior art, source owners and proof strength

* `DASHI/Core/FiniteC3OrbitStabilizerExact.agda`: exact group
  law and orbit/fixed-point distinction.
* `DASHI/Moonshine/C3FourierConjugationExact.agda`: exact
  depth-one symbolic cyclotomic Fourier rows.
* `DASHI/Moonshine/C3CyclotomicRealDescentExact.agda`:
  fixed 1D axis and conjugate 2D real plane; still a
  dimension/character bookkeeping owner, not a physical
  spectral theorem.
* `DASHI/Physics/Foundations/R3HodgeCrossExact.agda`:
  explicit R3 wedge -> Hodge star -> cross identification,
  with su(2) bracket twice the cross product. Its scalar
  carrier is an abstract real-analysis interface, not
  automatically the rational/Fp matrices below.
* `DASHI/Physics/Foundations/OrientedThreeAxisBracket369Exact.agda`:
  genuine oriented three-axis bracket and 3^3 phase chart,
  NOT a same-object isomorphism with the Monster.
* `DASHI/Physics/QFT/SpinorRepresentationReceipt.agda`:
  char 2 Clifford toy; warns that -1=+1 erases
  fermionic/spinorial central sign.
* `DASHI/Physics/QFT/DiracSpinSectorReceipt.agda`:
  conditional DHR/fermion receipts, NOT CAR
  localization or analytic Dirac domain proof.
* `DASHI/Wikimedia/IbrahimMonster3BWholeCharacterIsotypicBypassExact.agda`:
  explicit pinned mathlib Maschke/FDRep/isotypic
  source references, with a remaining whole-character
  semantic interface gap. The current C3 comparison
  does NOT discharge that actual Monster production.
* `DASHI/Foundations/BinaryPolyhedralMcKayDimensionExact.agda`:
  actual numerical McKay eigenvector identities and
  squared-dimension orders 24,48,120 for affine
  E6/E7/E8. It does not build all the irreps.
* `DASHI/Wikimedia/IbrahimEnZeroToThirteenNDimOEISHyperfabricSnowballExact.agda`:
  E_n/ternary-rank profile 3^n separate from
  exceptional E6, E7, E8 Lie and McKay diagrams.
  Do NOT identify these homonymous E_n constructions.

## Maschke comparator: SAME group action, coefficient changed

C3 acts on the existing rational xyz space by the same
ambient horn spatial map R(x,y,z)=(z,x,y).
R^3=I.

Over any field K where 3 is invertible, the Reynolds
projector is

    P=(I+R+R^2)/3,    P^2=P,    PR=RP=P.

It splits K^3 into

  fixed diagonal axis K*(1,1,1)             dimension 1,
  transverse plane {(x,y,z):x+y+z=0}       dimension 2.

On transverse basis v(a,b)=(a,b-a,-b), R acts
via A=[[0,-1],[1,-1]] (column convention).
A satisfies A^2+A+I=0.

The new Agda `AlexanderHornedC3MaschkeR3Exact.agda`
uses ACTUAL previously constructed rational horn
`Ambient.Triple ℚ`, with term-level nontrivial equalities:
Reynolds idempotence, rotation invariance, reconstruction
v=P(v)+(v-P(v)), an explicit transverse-plane chart,
zero-sum characterization, and exact companion-matrix
intertwiner. It cites the older symbolic fixed-1/transverse-2
cyclotomic modules rather than replacing them.

The finite-field comparison is SAME matrix A with
identical integer coefficients, reduced mod p:

    p=2: Maschke YES, A irreducible 2D, BUT -1=+1
         so spin/fermionic central sign vanishes.
    p=3: Maschke NO, A-I nonzero nilpotent with
         (A-I)^2=0. Characteristic polynomial
         X²+X+1=(X-1)², unique invariant line,
         NO invariant 1D complement. In K³ the
         all-ones diagonal also lies INSIDE sum-zero
         plane; J=I+R+R² is nonzero but J²=0.
    p=5: Maschke YES, A 2D irreducible (Phi3 has
         no root mod 5), and -1 != 1.
    p=7: Maschke YES, A has distinct roots 2,4;
         it splits as two 1D characters. Projectors
         P2=(A-4I)/(2-4), P4=(A-2I)/(4-2)
         have rank one, are orthogonal and sum to I.
         Spin central sign remains distinguishable.
    p=11: Maschke YES, irreducible 2D, spin sign visible.
    Q:  Maschke YES, fixed 1D + irreducible rational
         cyclotomic 2D transverse sector.

This answers the request to CONSTRUCT a truly semisimple
contrast, not to misleadingly infer a 'physical zero mode'
from F3 invariant vectors. The mod-3 fixed line is a
modular representation degeneracy. It changes nothing about
a Dirac Fredholm/kernel computation in characteristic zero.

Sources:
* Maschke theorem and group averaging:
  https://web.math.princeton.edu/~smorel/rep_theory_notes.pdf
  (Theorem I.3.2: |G| invertible in field iff KG semisimple).
* Terras, Fourier Analysis on Finite Groups and Applications
  (1999), existing original repo attribution.
* Serre, Linear Representations of Finite Groups,
  existing original repo attribution.

Exact arithmetic audit:
`scripts/alexander_horned_c3_maschke_field_comparison.py`
tests F2,F3,F5,F7,F11 and rational examples, includes
explicit F7 eigenprojectors and modular Jordan residue.
A locally run independent comparative check PASS.
Agda source written; kernel receipt not yet obtained.

## Full finite actor: F7 pays BOTH Maschke prerequisites

Groups already defined and supplied from the previous
literal 2I->A5 finite construction:

    Q_projective=(A5)^3 rtimes C3, |Q|=648,000.
    Q_spin=(2I)^3 rtimes C3, |Q|=5,184,000.

7 divides NEITHER order. Therefore ANY finite-dimensional
F7 representation of either entire group is semisimple.

Do not generalize the cyclic p5 result to the full group:
5 divides both group orders. Similarly 3 divides both;
both are modular in characteristic 3.

Our existing pointwise scalar state actors give finite
permutation modules:
  V_projective=Fun(C3 x A5,F7), dimension 180;
  V_spin=Fun(C3 x 2I,F7), dimension 360.

The actual 2-to-1 slot factor f:Omega_spin->Omega_projective
induces an injective equivariant pullback of functions.
The (central sign) fibre average
  E(h)(x)=(h(x)+h(-x))/2
is an equivariant idempotent because the ± kernel is
NORMAL in the full actor. Thus the 360 module admits
an explicit invariant direct-sum decomposition

    V_spin = V_even (+1 central sign) ⊕ V_odd (-1 sign),

each of dimension 180. Over F7 2 is invertible.
The even part is exactly the pulled-back 180-state
module; the odd part is a genuine additional spin-sign
observer, not a physical Dirac eigenstate.

There is also the global Reynolds mean (on the transitive
coordinate space) with denominator 360 / 180; its
naturality under pullback is checked concretely. Since
7 is also coprime to the WHOLE acting group orders,
Maschke supports ALL other invariant complements too.

A new finite audit
`scripts/alexander_horned_c3_full_actor_maschke_f7.py`
reuses the literal SL2(F5)->A5 120/60 map, tests 180/360
fibres, even/odd averaging and actor action equivariance.
Equivalent earlier local finite probes passed; the newly
committed exact script awaits an execution receipt.

## R3/spinor/E_n cross-pollination: no type erasure

The R3 Hodge/cross theorem says
  [u,v]_su2 = 2*(u x v).
The algebraic C3 rotor permutes axes x->y->z
in this same orientation-preserving geometry.

A precise next transport would require an actual
scalar embedding ℚ->ℝ into the `R3HodgeCrossExact`
owner, preserving +, *, its bilinear form and
the existing SU(2) Lie bracket. Then one may prove
C3 equivariance of the wedge/Hodge/cross and Dirac
principal symbol. Matching 3-axis names alone is
not that scalar map. No claim of full continuous
Spin3 covering-space formalization.

McKay is its own well-defined bridge:

   2T (24) -> affine E6,
   2O (48) -> affine E7,
   2I (120)-> affine E8.

The arrows are McKay character/tensor decomposition
GRAPH correspondences, not group homomorphisms into
exceptional Lie groups. The repo's actual E6/7/8
dimension skeleton matches the source facts.
Reference: Bertram Kostant, PNAS 1984
https://pmc.ncbi.nlm.nih.gov/articles/PMC391682/
and 2026 London Mathematical Society McKay retrospective
https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/blms.70245

No free identification of this exceptional E8 with
the 248-dimensional adjoint, the 240 roots induced
from spinors in separate literature, a 3^n 'E_n'
hypervoxel, or the Monster 3B irreducible sector.

## Decision/phase roadmap

DONE: C3 split/cohomology, exact quaternion q and
signed lift, R3 rational Maschke splitting source,
finite modular/nonmodular controls, explicit F7
full-actor candidate with additional spin-sign
representation.

NEXT PRIORITY: exact-head Agda kernel run for the
R3 Maschke module and upstream dependencies, repair
compiler errors rather than promoting status booleans.
Check the F7 actor audit in the focused workflow;
do not confuse a source-written theorem with success.

NEXT GEOMETRIC SAME-OBJECT: construct the particular
stagewise rotated horned ball and prove R(B)=B.
Then the flat Dirac C3 action on the open complement
has a geometric domain. For an analytic spectral
kernel claim choose and prove a self-adjoint domain.

LATER OPTIONAL: literal ℚ-to-existing-ℝ representation
transport for R3 wedge/Hodge, actual McKay irreducible
tensor graph or E8 pinor construction if it has
a distinct falsifiable target.

No new foundational C3 spin cover, no speculative
'physical zero mode' and no accidental promotion of
Monster or quantum-conscience claims.


## 2026-10-24 additional native characteristic-three proof

To avoid relying only on Python to classify the bad-characteristic
case, `DASHI/Mathematics/Topology/AlexanderHornedC3Mod3JordanExact.agda`
now defines the ACTUAL finite three-element field carrier (addition, multiplication, inverses and finite-law proofs)
`F3={f0,f1,f2}`, the two-vector carrier `F3²`, the
SAME cyclotomic companion operator

    A(a,b)=(-b,a-b),

and its nilpotent part `N=A-I`. It proves by exhaustive
nine-vector pattern matching:

    A³ v = v  for all v,
    N² v = 0  for all v,
    N(1,0) != 0,
    A(1,2)=(1,2), (1,2)!=0,

and the literal C3 group action composition law, borrowing
the existing `FiniteC3OrbitStabilizerExact` multiplication.
Together with the standard theorem that the ONLY simple
F3[C3] module is trivial, this gives a genuine nonsplit
self-extension in the underlying 2D representation.
We retain the distinction between this finite Agda
source-written theorem and successful Agda kernel verification;
no compiler success was returned.

The good-characteristic source owner remains the rational
`AlexanderHornedC3MaschkeR3Exact` and the characteristic
5/7 field test. No artificial one-to-one identification
of finite F3 with Q or R carriers is promoted.

### Closing the coefficient-field linearity gate

The F3 module now contains literal multiplication and explicit
constructor-normalised proofs for additive/multiplicative
associativity, commutativity, distributivity, identities and
nonzero inverses, plus ALL 81 cases of additivity and
ALL 27 cases of scalar homogeneity of the SAME cyclic
companion operator. These clauses are source-generated
exhaustive finite proofs, not a postulated `linear` Bool.
The no-Maschke nilpotent witness and C3 group law are thus
supported by an actual source-written F3-LINEAR action,
although the Agda exact-head kernel receipt remains open.


## 2026-10-24 completion: MINIMAL F7 spin4, faithful wreath spin12, scope of C3 projectors

The constructive bottleneck beyond ordinary Maschke has now been
paid in the exact finite witness library:
`Docs/topology/AlexanderHornedMinimalSpinF7C3E8MaxCut20261024.md`.

- `scripts/alexander_horned_icosian_f49_minimal_spin.py`
  constructs F49=F7(sqrt5), 120 golden-ratio unit icosians
  (8+16+96), their 2x2 determinant-one matrix algebra,
  scalar-restricts to faithful GL4(F7), and builds the
  *ACTUAL SAME GROUP* bijective map to existing SL2(F5)
  using (2,3,5) generators and all 14400 products.
  Central -1 acts as -I4. No rank <=3 representation
  of 2I over F7 can be nontrivial, because order-5
  elements generate 2I and 5 divides none of
  |GL1(F7)|, |GL2(F7)|, |GL3(F7)|.
  Thus 4 is the MINIMAL nontrivial F7 degree.
- The 2D spin actor exists over F49 and its Frobenius
  conjugate has a genuinely different order-5 trace;
  restricting scalars gives the 4D F7 module.
  Do NOT claim a 2D full-2I spin representation over
  bare F7 from the earlier C3/2T rotor example.
- `scripts/alexander_horned_full_actor_f7_spin12.py`
  builds a faithful GL12(F7) block-monomial representation
  of (2I)^3 rtimes C3: the C3 block permutation reveals
  the phase, each faithful GL4 block reveals one factor.
  The diagonal central (-1,-1,-1) maps to -I12.
  Faithful 12D is proved; **minimal 12D is NOT asserted**.
- `scripts/alexander_horned_f7_spin12_horn_meridian_bidi.py`
  welds the PREVIOUS actual commutator root q of the
  binary Hatcher source to the new SAME 2I quotient:
  m^3 maps to diag(-I4,I4,I4) != I12, but to identity
  in its A5 projectivization. The group-quotient
  statement is finite/abstract, not a wild pi1 theorem.
- `scripts/alexander_horned_f7_spin_c3_projector_scope.py`
  corrects a crucial FULL-group invariant trap.
  The central sign ± splits 360 sites into full-actor
  invariant 180+180 even/odd spaces.
  The further six rank-60 C3×C2 joint Fourier spaces
  are subgroup eigensectors ONLY: the C3 Fourier
  projectors do NOT commute with arbitrary nonuniform
  2I^3 factors. A literal counterexample was locally
  computed. The 180± subspaces may further decompose;
  no irreducibility claim is made.

Independent LOCAL Python arithmetic passed: 120 finite
icosians, exact 120-element SL2F5 isomorphism, 14400
quaternion and matrix products, determinant-one, F49/F7
Galois trace descent, degree obstruction, 18x18 selected
full-actor 12x12 products, six projector idempotents
and explicit noncentral counterexample, same root cube
in spin12 vs A5. No typecheck/CI status promoted.

Attribution: unit icosians and binary group sources
precede DASHI; see Choi & Lee 2018, DOI
10.3390/sym10080326, and the classical McKay
correspondence. Our finite F49/F7 scalar restriction
and exact group-map calculation is a new computational
derivation on these prior mathematical roots.

PRIORITY now moves to the GEOMETRIC SAME-OBJECT task:
concrete C3-invariant three-copy wild-ball embedding
with attaching collars and van Kampen stage identification.
The earlier `C3OrbitSolidExact` already makes arbitrary
seed-orbit set invariance exact, but it does not construct
the actual Hatcher wild seed or its gluing. Do not spend
more cycles proving an abstract C3 extension splits.
