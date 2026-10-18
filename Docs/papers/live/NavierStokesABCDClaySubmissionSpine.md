# Navier–Stokes A/B/C/D — Clay Submission Spine

Author: Johl Brown  
Status date: 2026-09-21  
Status: **submission-facing working manuscript / audit spine; not a claim of Clay acceptance or publication**

## 0. Claim boundary

The official problem requires one of the four alternatives A/B/C/D. This project
continues all four, but Goal 1 no longer treats them as the same kind of work.

- **A/B are theorem-production lanes.** Their remaining named seams are genuine mathematical obligations.
- **C/D are source-proof audit and manuscript lanes.** Their exact Clay propositions are already inhabited in the pinned Lean audit project; the remaining Goal-1 work is to verify that the imported construction/proof spine warrants those theorem terms and to present the mathematics independently and readably.

A/B formal work remains valuable, but it does not gate a Clay-facing C or D
manuscript if the source proof survives independent mathematical audit.

## 1. Frozen independent Clay statement

The independent Lean project \`dashi_lean4/ExternalClayNS\` contains
\`ClaySpec.lean\`, written against the Fefferman-style A/B/C/D statement.

- C quantifies over every \(\nu>0\), with smooth divergence-free rapidly decaying initial data, smooth rapidly space-time decaying forcing, and excludes every global smooth bounded-energy solution.
- D quantifies over every \(\nu>0\), with smooth divergence-free periodic initial data, smooth periodic forcing whose every displayed derivative has rapid time decay, and excludes every global smooth periodic velocity/pressure solution. Pressure periodicity is included.

\`Gap.lean\` proves the semantic bridge from the pinned comparator definitions
to this independent specification. \`ClauseAudit.lean\` unpacks and repacks
every C/D clause, so the official-condition surface is explicit rather than
hidden in a single theorem alias.

\`SubmissionAudit.lean\` bypasses the high-level \`ComparatorSolution\`
aliases and rebuilds the endpoints directly from the source theorem spines.

## 2. Alternative D — direct submission spine

\`\`\`text
NavierStokesR3.theorem_1_1_with_initial_rest
        |
        | compression + periodisation
        v
PeriodicPaper.periodic_corollary
        |
        | CandidateProperties.no_global_solution
        | periodic uniqueness / finite-slab agreement
        | unbounded speed at t = 1
        v
PeriodicPaper candidate + no global periodic solution
        |
        v
ComparatorBridge.option_D_of_paper_candidate
        |
        | independent semantic bridge
        v
ClaySpec.ClayOptionD
        |
        v
ClauseAuditD for every nu > 0
\`\`\`

### D theorem spine to present in the paper

Fix \(\nu>0\).

1. Construct the compact whole-space candidate supplied by the source theorem and compress its spatial supports into the interior of a fundamental cube.
2. Periodise the pre-singular velocity and pressure and periodise the forcing. The resulting fields are smooth on the required domains, spatially periodic, divergence-free, satisfy the forced Navier–Stokes equation before the singular time, and have zero initial velocity.
3. The forcing has compact future-time support. Smoothness plus periodicity and compact future-time support imply arbitrary polynomial time decay of every derivative uniformly in space; this is the exact force-decay clause required by D.
4. The source candidate has speed unbounded as \(t\uparrow1\).
5. Suppose a global smooth periodic solution with the same data and forcing exists. Restrict it to any compact pre-singular time slab. Periodic classical uniqueness identifies its velocity with the candidate velocity on that slab.
6. Smooth periodicity makes the hypothetical global velocity uniformly bounded on the closed slab through \(t=1\), while pre-one agreement transfers that bound to the candidate.
7. This contradicts the candidate's unbounded speed at \(t=1\).
8. Hence no global smooth periodic solution exists. The pressure is periodic throughout the comparator/Clay solution predicate, so the official erratum is included.

### D audit checklist

- [ ] quantifier order: for every \(\nu>0\);
- [ ] initial datum smooth;
- [ ] initial datum divergence-free;
- [ ] initial datum spatially periodic;
- [ ] forcing smooth on the required future domain;
- [ ] forcing spatially periodic;
- [ ] every spatial/time derivative of forcing has arbitrary polynomial time decay;
- [ ] candidate solves the \(\nu\)-viscosity equation before the obstruction;
- [ ] periodic velocity uniqueness is applied with exactly matching data and forcing;
- [ ] hypothetical global pressure is periodic;
- [ ] the contradiction uses the same candidate, force and viscosity.

The pinned Lean source path currently supports these clauses definitionally; the
manuscript must still expose the mathematical reasons rather than cite the
theorem term as authority.

## 3. Alternative C — direct submission spine

\`\`\`text
ActualCandidate.selected_candidate_one_with_initial_rest
        |
        | viscosity scaling
        v
NavierStokesR3.theorem_1_1
        |
        | same-force comparator bridge
        | whole-space finite-energy uniqueness
        v
NavierStokesR3.comparator_of_breakdown
        |
        | independent semantic bridge
        v
ClaySpec.ClayOptionC
        |
        v
ClauseAuditC for every nu > 0
\`\`\`

### C theorem spine to present in the paper

Fix \(\nu>0\).

1. Take the source compact whole-space candidate, scaled to viscosity \(\nu\). The initial velocity is zero.
2. The candidate forcing is smooth and compactly supported in spacetime. Hence every required derivative has rapid joint space-time decay.
3. Assume a global smooth bounded-energy whole-space solution exists with the same zero datum and the same forcing.
4. On every compact interval \(0\le t<T<1\), apply the source whole-space classical uniqueness argument. The compact candidate provides the local support/boundedness hypotheses; the hypothetical solution supplies the uniform finite-energy bound.
5. Thus the hypothetical velocity agrees with the candidate before \(t=1\).
6. The candidate's terminal obstruction/unbounded-speed property rules out a smooth continuation through the singular time.
7. Therefore no global smooth bounded-energy solution exists for those data.

### C audit checklist

- [ ] quantifier order: for every \(\nu>0\);
- [ ] initial datum is genuinely \(C^\infty\);
- [ ] initial datum divergence-free;
- [ ] rapid decay of all initial derivatives;
- [ ] forcing genuinely smooth;
- [ ] rapid joint space-time decay of all displayed derivatives;
- [ ] exact Clay bounded-energy class, not a stronger substitute;
- [ ] whole-space uniqueness hypotheses match that class;
- [ ] same forcing and viscosity are retained through the bridge;
- [ ] the final exclusion is exactly of global smooth bounded-energy solutions.

## 4. Alternative A — remaining theorem-production seam

A is not gated by generic measure-theory formalisation. The local analytic
pieces already prove the essential near-origin and high-frequency envelopes.
The live mathematical cut is

\`\`\`text
actual Euclidean Fourier NS trajectory
        |
actual physical resolvent kernel
        |
        +--> near-origin saturation theorem already proved
        |
        +--> high-frequency curvature theorem already proved
        |
exact kernel/projected-Gram/resolvent identification        OPEN
        |
state majorant = finite-energy convolution majorant         OPEN
        |
concrete high-region inverse-sixth multiplier instantiation
        |
existing L1 / convolution / tail compilers
        |
A continuation/endgame
\`\`\`

The live Agda owner
\`NSClayFacingAPhysicalSameObjectCutExact.agda\` records that the near-origin
analytic estimate and high-frequency curvature estimate are closed while the
actual kernel same-object instantiation and finite-energy majorant identification
remain open.

### A submission obligations

The A paper cannot cite a generic carrier theorem without proving that its kernel
is the actual Navier–Stokes Fourier resolvent kernel. It must identify on the same
interaction:

1. output frequency \(\xi\);
2. pair resolvent;
3. output resolvent;
4. centered residual;
5. signed projected Gram scalar;
6. saturation coefficient used by the low-frequency theorem;
7. raw state majorant with the convolution quantity controlled by kinetic energy.

Once those equalities are explicit, the low-frequency singularity is cancelled
by the already-proved saturation estimate and the high-frequency branch is
handled by the existing curvature/inverse-power envelope.

## 5. Alternative B — primary live signed-reserve route and legacy route

The **primary R823--R825 path** is no longer the legacy B1--B7
physical-shell compiler. The preferred current physical finite-Galerkin
payment is at the **single shared** R408 viscosity
`delta = nu > 0`, for each selected cutoff and terminal.

```text
R408/R648 live finite trajectory
       |
R745 -> R760 -> R781
       |                        R822
       |               original CC rows + comparable certificates
       |                        |
R813 fully-separated     original signed CC scalar
  four-helicity work             |
       +---------- R823 ---------+
                    |
    V_N(T) = integral (D_CC + 6 nu d_N)
    A_N(T) = 2 integral (Q_sep - 9 N_sep)
                    |
    OPEN B-RESERVE: A_N(T) <= V_N(T)  for all admissible
                    |
      R821 / R735 critical energy barrier
                    ^
                    |
    OPEN B-W1: W_N(T) + Q_+-,N(T) <= B(T) (cutoff independent)
                    |
    OPEN uniform-in-N continuation AND universal initial-data bridge
                    |
      NSConcreteLiteralClayABCDRunTargetExact.LiteralB K
                    |
      NSConcreteLiteralClayABCDRunTargetExact.runTargetFromB
```

**New physical feasibility cut:**

- `NSTriadKNR650PhysicalCCGradedReserveRound824Exact.agda`
  uses R760 on each **R822 original incidence**. It proves the CC
  signed row is exactly a nested forcing contribution minus a
  dyadic production contribution. Comparable representatives remain
  attached as geometry certificates, not as substitute source scalars.
- `NSTriadKNR650PhysicalReserveFeasibilityRound825Exact.agda`
  proves that the *complete integrated R823 rate*, on the same live
  physical system and integration authority, equals the integral of
  the quadratic viscous, full nested high, and full dyadic low pieces.
  Its decision function returns either an actual reserve-payment
  certificate or a negated payment certificate **once concrete
  rational physical integrals are supplied**. It supplies neither an
  evaluated witness nor a signed inequality by itself.
- A physical counterexample to the universal auxiliary reserve
  estimate would reject this B auxiliary route only; it would **not**
  refute Fefferman B or the Navier--Stokes equation.
- R214 excludes using shell-width localization **alone** to pay the
  between-partner Gram debt. Do not infer a CC bound merely from
  R822's comparable representative.

**Important carrier-to-Clay gap:** R823–R825 are parameterised by a
rational finite Fourier/Galerkin system, abstract time, and an explicitly
supplied rational-valued integration authority. Even a proved reserve bound
on these carriers would require its actual continuous-time realization,
cutoff-uniform real/complex extension, the full arbitrary smooth periodic
initial-data quantifiers, and a continuation passage before it can inhabit
`NSConcreteLiteralClayABCDRunTargetExact.LiteralB K`. Neither the rational
decision procedure nor a finite selected-cutoff barrier supplies these
by itself.

**No duplicate B compiler is required:** R823 already contains
`allCutoffsSignedReserveBarrier`; R821 and R735 own the conditional
barrier. The remaining mathematical inputs are actual B-RESERVE,
independent B-W1, and a continuation/universal-data theorem matching
the canonical `LiteralB K` predicate. A barrier for a selected
trajectory is not the all-data theorem.

**Legacy B1--B7 remains an alternative sufficient route.** B1/B7 are
physical extraction/identification seams; B2/B3/B4 are analytic
estimates. They are not extra assumptions automatically imposed on
the R823 route. The ownership remains
`NSClayFacingBResearchCutExact.agda`.

**Other Clay alternatives are independent:**

- A: `NSClayFacingATwoPhysicalSeamCompilerExact.agda` still
  requires its actual Euclidean resolvent-kernel and state-majorant
  identifications plus whole-space continuation; R823 does not
  discharge these.
- C/D: `NSClayFacingCDSourceAuditExact.agda` and
  `NSClayFacingABCDProofStatusExact.agda` track external source
  alignment and optional local reconstruction, separate from an
  independently checked conventional proof and CMI adjudication.
  No periodic B barrier is used to prove forced breakdown.
- All four terminal theorem *types*, including the pressure
  periodicity clause in D, are owned by
  `NSClayLiteralABCDExact.agda`; the canonical run target is
  `NSConcreteLiteralClayABCDRunTargetExact.agda`. The latter
  consumes a genuine literal A/B/C/D proof term, never a Boolean
  receipt, selected-trajectory estimate, or GitHub status.

## 6. Submission policy

A theorem-assistant receipt is evidence, not the manuscript.

For C/D, do not write “proved because Lean says so.” The Lean project establishes
that the source theorem, comparator statement and independent Clay statement line
up. The paper must independently state the construction, decisive estimates,
uniqueness theorem and contradiction.

For A/B, do not promote compiler closure while any named mathematical seam above
is open.

The submission package should contain:

1. a self-contained main proof for the chosen successful alternative;
2. a clause-by-clause appendix against the official Fefferman statement;
3. a provenance appendix listing every imported standard theorem and every source-specific lemma;
4. machine-readable Lean/Agda audit artifacts as supplementary material;
5. exact commit hashes for all supplementary formal artifacts.

## 7. Stop condition

A lane is submission-ready mathematically only when:

- no named source-specific mathematical lemma is merely assumed;
- every official hypothesis is discharged on the same data/forcing/viscosity;
- every standard external theorem is cited with hypotheses checked;
- no semantic bridge strengthens the antecedent or weakens the conclusion;
- the human proof can be read without trusting the proof assistant.

Under this standard, C/D are finite referee-audit/manuscript tasks. A/B still
contain explicit theorem-production obligations. Stale Boolean ledgers or the
amount of formal infrastructure remaining below the paper layer do not alter
that mathematical classification.

## 8. 2026-09-30 R828: direct rational finite-Fourier feasibility result (newer than historical B1–B7)

This section supersedes the *research priority* in section 5, but does not
delete the earlier sufficient B1–B7 route. The latest periodic development
R745–R823 produces the canonical signed reserve payment at delta=nu:

  integral [ 18*Nsep - 2*Qsep + D_CC + 6*nu*d_N ] dt >= 0.

The new [R828 3-4-5 mathematical witness](NSR828Rational345FourierWitness.md)
does **not** assume this estimate: it evaluates its complete R815-style
physical Fourier scalar at an explicit smooth real divergence-free mean-zero
initial state in the radius-four cube, with the normalization

  commutator coherent work = -557627/125,
  critical production = 0, critical dissipation = 15834,
  complete signed initial rate = -28273644/125 < 0.

An independent conservative rational Lipschitz/ODE enclosure yields a
positive real-time interval with negative integrated scalar for the ordinary
finite Fourier polynomial dynamics. This is a mathematical falsification
candidate for the *auxiliary universal B reserve inequality*; it is never
a counterexample to Navier–Stokes itself.

The actual Agda R408 specialization is Q-valued and requires global
helical projector laws, whereas the real physical Fourier flow is
real-valued. Even though the selected 3-4-5 active helical snapshot is
rational, this does not fill the global Q-projector or genuine continuous
time dynamics interface. The exact R408/R692 scalar identification is
still a kernel/source-verification seam. Do not claim unconditional
certification of a false payment before discharging it.

If the literal source scalar weld succeeds, retire universal B-RESERVE as
a potential route: retain the exact R822/R823 identities as identities,
and pursue a **different** analytic inequality or the older independent
B1–B7 signed route, plus W1/continuation. Avoid adding new compilers
assuming the disproven hypothesis. The A resolvent work is logically
independent; C/D remain externally attributed forced-case source audits.


## 9. 2026-10-02 max-cut after R829--R832

The R828 decision route is now separated into theorem-bearing closed
infrastructure and exactly two physical leaves.

Closed/source-written surfaces:

1. R829B evaluates the eight exact mixed/commutator vectors through the literal
   R692 coherent-work consumer.
2. R829C evaluates the six production/dissipation rows from exact
   velocity/forcing vectors.
3. R829A aggregates those rows and R829 normalizes the canonical
   (6(12C-P+d)) scalar.
4. R830 kernel-targets the exact rational horizon/negative upper-bound
   arithmetic.
5. R831 proves the logical implication
   [
   	ext{selected integrated complete rate}<0
   Longrightarrow
   
eg(	ext{R823 demand}le	ext{R823 reserve}).
   ]
6. R832 records that no further reserve estimate is required after the two
   remaining physical leaves.

The exact remaining B-decision cut is

[
oxed{
	ext{D1 repository operator evaluation}
+
	ext{D2 real finite-Galerkin transport}.
}
]

D1 is now the finite record
`Repository345VectorEvaluation`: prove the actual repository
`fixedOutputMixedProduct`, `fixedOutputCommutator`,
`Audit.velocityAt`, and `Audit.projectedNonlinearity` values equal the
already kernel-targeted vectors on the radius-four state.  The global
`PeriodicHelicalProjectorLaws ℚ` record is explicitly not part of this
instantaneous theorem.

For D2, Round71 already constructs the fixed-cutoff autonomous
reality-preserving Galerkin vector field.  The Lean companion now factors the
standard analytic part as:

[
	ext{linear + bounded bilinear diagonal}
Longrightarrow C^1
Longrightarrow 	ext{local real integral curve},
]

followed by the already-source-written displacement/Lipschitz-to-negative-
integral theorem.  Hence the remaining Navier--Stokes-specific real-ODE work is
to identify the Round71 coordinate field with that quadratic template and
verify that the explicit R828 bootstrap constants apply to the selected
solution.

### Post-decision periodic B

If D1+D2 produce the selected negative integral, freeze universal R823
B-RESERVE as a false auxiliary conjecture.  The surviving positive B cut is
exactly

[
oxed{mathrm{B1+B2+B3+B4+B7+Bcont}}.
]

The existing B1/B2/B3/B4/B7 shell/payment/decomposition compilers are already
closed and are not counted as separate leaves.

### Whole-space A

`NSClayFacingAMaxCut20261002Exact.agda` records exactly three remaining jobs:

[
oxed{mathrm{A1 kernel+A2 majorant+A3 continuation}}.
]

The canonical near-origin pair resolvents are already constructed directly by
`NSWholeSpaceCanonicalPairSaturationOriginExact.agda`; an abstract physical
kernel is not required for that local theorem.  Generic Young/Cauchy and
inverse-sixth tail integration are likewise outside the research cut.

### C/D

`NSClayFacingCDMaxCut20261002Exact.agda` makes source-coordinate audit
completion independent of optional DASHI Fourier/369/R406 reconstruction.
C/D manuscript reconstruction and independent referee checking remain
publication/audit work; optional internal representation welds do not gate the
official-coordinate source audit.

This is the current hard stop condition: do not create new compiler layers
unless one of the named leaves proves that a genuinely new mathematical
quantity is required.


## 10. Round71/74 cross-pollination into R830

The R830 real-ODE leaf is smaller than the first R828 handoff suggested.

Existing theorem-bearing owners already provide:

- `NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact`: one autonomous
  fixed-cutoff Galerkin vector field with reality built into the phase space;
- `NSTriadKNFixedCanonicalTransverseInvariantRound71Exact`: the transverse
  subspace is invariant;
- `NSTriadKNFixedCanonicalVectorFieldDegreeTwoRound71Exact`: the literal
  Round71 RHS is represented by an exact expression of algebraic degree at most
  two and that expression evaluates to the literal RHS;
- `NSTriadKNFiniteRationalSlotAssignmentBridgeRound74Exact`: the corrected
  finite slot chart is executable and the earlier quantitative local-Lipschitz
  estimate already applies through it.

The standard complete-real side is now isolated in the Lean modules
`Rational345LocalODE`, `Rational345QuadraticODE`, and
`Rational345ShortTime`: a linear-plus-bounded-bilinear real field is (C^1),
has a local integral curve, and the exact R828 constants satisfy the entire
short-time sign budget.

Accordingly `NSTriadKNR650Rational345RealODEMaxCutRound833Exact.agda`
reduces R830 to only two NS-specific bridges:

1. physical Round71 RHS = corrected finite-real quadratic/chart field;
2. the selected R828 displacement and rate-Lipschitz bounds apply to that
   solution, with the selected scalar identified with the R829/R815 scalar.

Reality, transversality invariance, polynomial degree, generic Picard theory,
and the huge rational (KLT) arithmetic are not separate open leaves.

The post-reserve B continuation cut is also non-circular: the standard
localized Luo continuation compiler is already constructed, while the
cutoff-uniform/continuum inputs needed to turn the eventual B1--B7 estimate into
the all-data global theorem remain the explicit B-continuation leaf.
