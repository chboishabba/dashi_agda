# Horned C3 × lepton SU(3): steelman, phase gates and deliverables — 24 October 2026

**Canonical consumer:** PR #1247 (neutrino, CP, Q(ζ₃)); topology owner:
PR #1244 (Alexander horn and C3); independent KK-holonomy consumer:
PR #1241. This is the **current decision-grade status**, superseding
older chronological "missing group representation", "nontrivial orbit
implies new physics", and "committed Python NOT RUN" roadmap wording
*only to the precise extent established below*.

## Primary roots, ownership, epistemic grades

- **J. W. Alexander (1924)**: original horned sphere.
- **Allen Hatcher**, *Algebraic Topology*, Example 2B.2:
  injective free-group commutator direct limit for the *single*
  horned complement; not a proof of the three-copy geometric embedding.
  https://pi.math.cornell.edu/~hatcher/AT/AT.pdf
- **Morikuni Gotô**, *A Theorem on compact semi-simple groups*,
  *J. Math. Soc. Japan* 1 (1949), 270–272:
  every element of connected compact semisimple **ambient** SU(3)
  is a GROUP commutator.
  https://doi.org/10.2969/jmsj/00130270
- **Cecilia Jarlskog**, *Phys. Rev. Lett.* 55 (1985), 1039,
  https://doi.org/10.1103/PhysRevLett.55.1039 :
  basis-independent CP and rephasing invariants.
- **Neutrino global-fit inputs**: NuFIT v6.1 (2025), and original
  experiment-specific T2K and IceCube analyses; these are separate
  observation roots, not consequences of C3/horn topology.
- **Existing DASHI source owners**: CompactLieGroupCore,
  CompactLieGroupDerived, SUNMatrixCarrier, SUNMatrixLieGroup,
  SU3MatrixInstance, canonical Q(ζ₃) algebra, qutrit matrices,
  CPPhaseStructuralOriginReceipt / JarlskogDiagnosticAnalysis,
  horned PR #1244 and neutrino PR #1247.
  A source-written proof is never a kernel theorem without an
  actual compiler receipt.

## The strongest defensible steelman

Let G_A be Hatcher's abstract commutator-tower group. Every
A∈SU(3,C) has a group commutator factorization by Gotô;
recursively choosing factors supplies compatible free-group
homomorphisms and hence, by the direct-limit universal property,
a homomorphism rho_A:G_A→SU(3,C) sending the distinguished
meridian m to A.

For three formal horn factors G=G_A*G_A*G_A and the factor-cycle r,
the selected unitary T=diag(1,ζ,ζ²) with T³=I gives an equivariant
representation of the abstract semidirect K=G⋊C3:

    rho_j(g)=T^j rho_A(g) T^-j
    R(g,j)=rho(g) T^j.

The model's specified CP-nonzero example
A=T(2|u1><u1|-I) lies in SU(3,C); the exact rational cyclotomic
field-trace obstruction proves A infinite order using the
standard algebraic-integer theorem. Thus the abstract image is
infinite. **This genuine existence statement is PAID
mathematically**. Gotô is NOT proved anew in Agda.

The positive steelman is a physically sourced flat SU(3) holonomy
model after a genuine smooth exterior pi1 identification,
an independently justified connection/holonomy choice, and an
action coupling specified charged lepton matter to it.
Then e.g. a Wilson character tr rho(m) could in principle
discriminate that source holonomy from a trivial connection.
None of those physics inputs is currently supplied.

## Two new decisive negative/discriminator results

### A. Threefold inner orbit is a rephasing orbit, not new neutrino physics

The exact algebraic witness
Ad_T(A)≠A demonstrates a three-member matrix orbit.
But charged-lepton row rephasing U' = T U leads to

    Hnu' = T Hnu T†
    |U'_(alpha,i)|² = |U_(alpha,i)|²
    J(U')=J(U) !=0
    amplitude_(alpha→beta)(U')
      = T_beta amplitude_(alpha→beta)(U) conj(T_alpha).

Therefore EVERY coherent vacuum oscillation probability,
and every phase-averaged astrophysical source flavour ratio,
is exactly unchanged. Simultaneously transforming the
charged-current basis yields the same physics.
A new physical interaction cannot be inferred merely by
relabeling or fixing a phase convention.

The stronger Wilson-character statement is independent of
the PMNS construction:

    rho(r(g)) = T rho(g) T^-1
    χ(r(g))=tr rho(r(g))=tr rho(g)=χ(g)

for every word g, and similarly for simultaneous C3 rotations
of a product of words. Thus all single-loop character/Wilson
traces are blind to the difference between these rotated
representatives, despite distinct matrices. A physical
discriminator requires a specified *relative* source, geometry,
coupling/boundary condition, or symmetry-breaking order parameter
whose fully gauge-invariant observables genuinely differ.
Do NOT interpret three orbit points as three measured generations.

**New source:** `NeutrinoHornedC3RephasingNoGoExact.agda`;
nine finite Born clauses, exact quartet equality, nine
mass-operator covariance clauses, and two exact character
equalities (source-written, no Agda kernel receipt).
**New source-hash matched test:** 
`tests/test_neutrino_horned_c3_rephasing_steelman.py`;
seven exact Fraction test methods passed, covering coherent
all-channel amplitudes, J, mass operator, source mixtures,
and Wilson-word traces. It is a direct mathematical
counter-discriminator, not an experimental exclusion.

### B. Q(ζ₃)-points are not the compact analytic SU(3) of Gotô

The field K=Q(ζ₃) has degree two over Q. Its special-unitary
K-rational matrix group is a **countable subgroup** of
the compact Lie group SU(3,C); the former is not itself
a connected compact Lie group under the induced topology.
Consequently Gotô's global theorem CANNOT be instantiated
merely by filling an abstract `CertifiedSUNMatrixTheory 3`
over K and declaring the result connected and compact.

Specific exact witness: for the diagonal target
T=diag(1,ζ,ζ²), the cyclic-P factorization takes
D0=diag(1,ζ²,1), det(D0)=ζ². To rescale D0 to det=1
requires s³=ζ, i.e. a **primitive ninth root of unity**.
Its cyclotomic polynomial Φ9(x)=x⁶+x³+1 is irreducible
over Q and has degree 6; it is not contained in the
degree-two field Q(ζ₃). Therefore THIS standard
cyclic/spectral SU(3) commutator witness cannot be
made wholly inside K by a common phase rescaling.
This does NOT prove no alternative commutator factors
exist in the K-rational group.

**New committed test:**
`tests/test_neutrino_cyclotomic_vs_analytic_su3.py`,
3/3 exact SymPy/Fraction tests, source-matched.
**Correct repair:** embed the exact K-root via the
specific complex embedding ζ↦-1/2+i√3/2 into the
analytic SU(3,C) matrix group, then use Gotô there;
do not require the infinite recursive image to remain
inside K without a separate theorem. The exact
matrix-target weld is useful for algebraic identities,
not an automatic completion/topology theorem.

## Phase and deliverables register

| Phase | Deliverable / owner | Status | Acceptance criterion |
| --- | --- | --- | --- |
| P0 Provenance | Original Alexander/Hatcher/Gotô/Jarlskog/NuFIT roots, canonical DASHI owners | **PAID** | Separate source, source-written, kernel, empirical grades |
| P1 Algebraic witnesses | Finite horn A5 actor, exact C3, same-space complex PMNS/Jarlskog, SU3 root, nonintegral field trace | **PAID as exact computations** | Git-blobs + exact Fraction and SymPy regressions |
| P2 Abstract topology/group existence | G_A→SU(3,C) infinite image; formal K→SU(3,C) C3-equivariant action | **PAID in ordinary mathematics; partial Agda** | Published Gotô/Hatcher hypotheses; no false finite-quotient factorization |
| P2b Algebraic/analytic bridge | Embed K-points in actual connected analytic SU(3,C), avoid false compactness claims | **NOT TYPE-CLOSED** | Explicit chosen embedding, group homomorphism and valid commutator target carrier |
| P3 Formal certification | Agda checked matrix theory, function/record extensionality, abstract colimit, complete Gotô statement | **OPEN** | Literal compiler output at fixed head; Python is not kernel |
| P3b Topological source | Smooth three-copy horn exterior and actual pi1 plus chosen flat bundle | **OPEN** | Explicit manifold/embedding/van Kampen/collar and same-object representation |
| P4 Physical model | Gauge-/basis-invariant interaction/holonomy selection, lepton mass/current terms, symmetry-breaking discriminator | **UNSTARTED as physical derivation** | Fixed action and independent, non-rephasing observable with no free post-hoc fit |
| P5 Experimental | Predict parameter-independent or bounded-fit outcome and compare with original NuFIT/T2K/IceCube correlated likelihoods | **OPEN** | Versioned likelihood, nuisance profiling, observed-vs-predicted register |
| P6 Other programs | KK/graviphoton, E6/Monster/VOA, 369/729, quantum gravity | **NO SAME-OBJECT IDENTIFICATION** | Full equivariant spectral/interaction map and independent measurements |

**Current programme phase:** mathematically **post-existence P2**,
source-formally **P2/P3 interface**, **pre-physical-model P4**
and **pre-empirical-validation P5**. This is NOT “one easy remaining
compiler round” to a neutrino/TOE proof.

## Max-cut Pareto and steelman decisions

1. **Highest-information next cut: choose a physical discriminator.**
   Specify the source spacetime, charged fermion representation,
   interaction and potential/background that produce an observable
   different from a row-rephasing transformation. If there is no
   such invariant after quotienting by basis freedom, RETIRE the
   claimed generation/CP prediction rather than expanding encodings.
2. **Formal weld only as a supporting cut:** use the existing
   `SUNMatrixCarrier`, `SU3MatrixInstance`, nine-cell
   `QutritMatrixGates.Matrix3`, and explicit K→C embedding.
   Pay universal polynomial laws and matrix equality. Run Agda
   locally when available; use exact Python now without calling
   it a kernel theorem. Gotô is analytic, not a K-point axiom.
3. **Geometry is independent, not a shortcut:** pay the three-copy
   physical exterior pi1 and a specified flat connection before
   promoting its holonomy into a field theory.
4. **Prediction beats further analogy:** preregister a constrained
   physical PMNS/CP/Δm² ratio test before looking at NuFIT/T2K.
   A theorem holding for *every* A∈SU3 is not a prediction.
5. **Keep other programmes separate:** KK U(1) photon, colour SU3,
   VOA Monster action and finite A5 quotient do not become physical
   lepton flavour simply by sharing a Lie algebra or C3 character.

## Exact local execution receipts

At current branch read-back:
- Earlier **26/26** committed-source unit tests remain passed.
- New CP rephasing + Wilson character **7/7** exact tests PASS.
- New cyclotomic/analytic field boundary **3/3** tests PASS.
- Total selected cross-PR **36/36** source SHA-matched unittest
  methods PASS with Python 3.13.5; SymPy 1.14.0 independent universal
  symbolic 3x3 Q(ζ₃) algebra **10/10** polynomial laws PASS.
- Source exact Git blobs:
  rephasing test `c75fbb54da1f9b7ac6bc3e1b3e0998913e0e1665`;
  field test `09700969a3ae1e5c02a8dcaa8f1a9cb62718c9d6`.
- New Agda module was source-read-back, but **NO Agda kernel run**.
- No new NuFIT likelihood, detector data, real-world horned holonomy
  or physical neutrino CP prediction was obtained.

See corresponding machine-readable
`logs/research/neutrino_horn_c3_steelman_phase_receipt_20261024.json`.

## 2026-10-24 P4 max-cut: observational and regularity priorities

A new decision-grade **high-payoff** roadmap is at
`Docs/physics/HornedSU3ObservableRegularityParetoMaxCut20261024.md`.
It preserves the earlier rephasing no-go but adds a genuine
**independent gauge-invariant toy observable**, the precisely
bounded horn regularity obstruction, and source-derived
spectral-selection priorities. This is the canonical consumer,
not another C3 group or cloned Wilson module.

**Biggest mathematical opportunity (first):** conditional
shrinking-horn gauge regularity obstruction. For unitary
holonomies \(U_w\) with \(U_w=[U_{w0},U_{w1}]\),
\(\|[X,Y]-I\|\le2\|X-I\|\|Y-I\|\).
At level n, if every leaf has defect at most ε_n, then
\(\|U_{root}-I\|\le(2ε_n)^{2^n}/2\).
The actual nontrivial root has norm gap δ≈1.43818847527,
therefore SOME descendant at every depth has defect
at least \((2δ)^{1/2^n}/2\to1/2\).
Thus if actual physical representative loops shrink
uniformly in length and the connection remains bounded
in compatible frames, such a nontrivial root is impossible.
**Uniform shrinking actual geometric loops are still
an unverified hypothesis**, NOT a consequence of Hatcher's
abstract free-group tower. Source analytic prior owner:
`DASHI/Geometry/FlatFormalDiskHolonomySurface.agda`.

**Highest engineering/experimental prototype (second):**
non-Abelian two-arm interference from canonical
`SUNWilsonClassFunction`/ `SUNWilsonAction`.
Selected *post hoc* W=TS1 has exact
\(Tr(W)=(176093404722400-19836986431118ζ)/181846007130841\).
An unpolarized qutrit with two 50:50 transports (I,W)
has \(P_+(0)=434928608401/648677790003≈0.670484816\),
vs 1 for identity W. Gauge invariant and nontrivial
*in the specified toy*; not a physical PMNS prediction.
An ordinary single puncture/circle can reproduce **any**
single-loop W. Even a nontrivial commutator loop in the
two-generator free group is not horn-specific.
Horn identification requires nested geometric source
and multi-scale compatible loops. Prior experimental
sources: Nat Commun 2019 DOI 10.1038/s41467-019-10974-8;
npj Quantum Inf 2021 DOI 10.1038/s41534-021-00483-2.

**Highest physics mechanism prospect (third):**
original Hosotani 1989 Wilson-line quantum potential,
DOI 10.1016/0003-4916(89)90015-8.
Pure classical \(F=0\) exterior Yang-Mills stress/action
does **not** select W; source-specified matter/geometry,
renormalized spectral determinant and symmetry/anomaly
authority are required. Synthetic S1 ring heat trace
for chosen W at t=.2 is 2.25351710695 vs 3.00223408384
for W=I: a distinct gauge-invariant spectrum, but
another proof the effect is not inherently horn-specific.
No chiral SM lepton SU3 gauge anomaly cancellation is
asserted. This route reuses existing Dashi covariant
spectral/KK machinery only after a same-object action.

**Revised P4 acceptance:** source-defined (not fitted)
physical connection/boundary or loop-effective action,
anomaly-safe matter currents, actual geometric pi1 and
physical loop family, a strictly gauge-invariant
*horn-specific* observable, and a quantitative outcome
not reproducible by a trivial/ordinary-puncture
counterfactual. P5 then compares source experiment
likelihoods. A finite synthetic demonstration is a
valuable engineering outcome, **not** physical horned
spacetime or neutrino mass discovery.
