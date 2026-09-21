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

## 5. Alternative B — remaining theorem-production seam

The current B route is the literal physical infinity-shell route:

\`\`\`text
B1  R236-filtered physical DFL
    -> literal InfinityShellSupport receipt

B2  literal DFL x DHH shell-pair signed estimate

B3  literal DHH intra-shell signed l2 aggregation

B4  critical-touching signed operator estimate with theta < 1

B7  literal R406 remainder
    = 4 * sum of the live fixed-output covariances
\`\`\`

Classification:

- **B1/B7:** exact same-object/extraction identities;
- **B2/B3/B4:** genuine analytic estimates.

A publishable B proof must state and prove these five claims directly in
conventional mathematics, then show how they imply the periodic continuation
criterion. Agda remains the preferred discovery/checking environment because
its physical carrier and signed block machinery are already exact.

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
