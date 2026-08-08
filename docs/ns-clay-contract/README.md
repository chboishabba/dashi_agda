# Navier–Stokes Clay contract

This directory is the normalized entry point for the periodic Navier–Stokes Clay route.

## Answer to the three questions

### 1. Was the true Clay requirement already implemented?

Not exactly before Round 23.

The repository already had a strong submission-shaped interface and a long terminal composition. It correctly kept the Clay promotion flag false. However, the older interface was not a literal transcription of Fefferman’s periodic alternative (B): it added a mean-zero datum requirement and pair uniqueness, while it did not expose positive viscosity, three spatial dimensions, zero forcing, velocity periodicity and the pressure-periodicity erratum as separate clauses.

Round 23 adds the literal theorem type in `NSTriadKNFeffermanPeriodicClayStatementExact.agda`. It removes the extra mean-zero and uniqueness requirements and lists every official precondition and postcondition separately. Constructing the theorem type is complete; inhabiting it for the physical carrier remains open.

### 2. Is there enough repository content to identify a path?

Yes. There is now a single explicit composition rather than several overlapping terminal stories.

The in-repository route is:

1. finite Galerkin filtered-vorticity equation and critical enstrophy identity;
2. pair-input-frequency defect damping;
3. uniform taxation of all physical forcing classes;
4. strict viscosity margin and Grönwall;
5. shell and Galerkin cutoff limits;
6. critical restart past a hypothetical finite maximal time;
7. smooth velocity and pressure recovery;
8. legacy-to-literal Clay witness adapter;
9. Galilean restoration from centered data to arbitrary periodic data.

The reducers for steps 2, 4, the order-theoretic part of 5, the contradiction logic in 6, and the terminal composition are present. The open mathematics is concentrated in the physical estimates and analytic limit producers listed in [requirements.md](requirements.md).

Round 24 adds a broad [claimed-paper corpus](paper-corpus/README.md), including low-authority and claimed-solution papers. Each source is mapped to its first load-bearing physical lemma, and exact countermodels are retained where a displayed implication fails.

Round 25 closes the discrete support part of that path. The [literal physical carrier and five-class support tranche](physical-carrier-support-round25.md) proves duplicate-free output fibres, the low-low-to-far-high obstruction, exhaustive and unique physical triad classification, and exact `HH+LH+HL+CC+Com` recomposition. L4 is now checked exact; L3 is narrowed to finite-dimensional continuum ODE existence and constraint propagation.

### 3. What are the preconditions, postconditions and invariants?

They are defined in [requirements.md](requirements.md) and formalized by `NSTriadKNLuoClayPrePostInvariantContractRound23Exact.agda`.

The dependency-ordered statement of the remaining mathematics is in the [highest-alpha lemma ladder](paper-corpus/highest-alpha-lemma-ladder.md).

## ZKP orchestration frame

- **O — Organization:** `DASHI/Physics/Closure`, the paper-facing theorem interfaces, validation scripts and this documentation surface.
- **R — Requirement:** Fefferman periodic alternative (B), including the pressure-periodicity erratum.
- **C — Code:** Round 22 finite Galerkin and defect modules; Round 23 literal contract, adapter and Galilean reduction; Round 24 claimed-paper corpus and normalized ladder; Round 25 literal carrier certificate and physical support closure.
- **S — State:** theorem type, terminal reducers and L4 physical support implemented; the physical theorem remains uninhabited.
- **L — Lattice:** finite PDE → critical tax → strict absorption → nested limits → restart → smooth global witness → literal Clay witness.
- **P — Proposal:** work only on physical producers that move a clause from `physicalProducerOpen` to `checkedExact`/`checkedReducer`, or source audits that rigorously falsify a proposed producer.
- **G — Goal:** inhabit the literal periodic Fefferman statement for every positive viscosity and every smooth divergence-free periodic datum.
- **F — Gap function:** count of load-bearing open producers, weighted first by scaling correctness, then cutoff uniformity, then strict viscosity margin.

## Updated plan and roadmap

The target theorem is literal, mean zero is a reduction rather than a Clay precondition, and physical support is now tied to the actual cutoff `Z³` carrier.

- Frame all further work around the literal periodic Fefferman statement.
- Search broadly, including unconventional, unreviewed and incorrect papers.
- Preserve valid local lemmas even when a terminal proof fails.
- Keep one non-overlapping lane for each open physical producer.
- Do not assign work to terminal composition, nested-limit logic or restart contradiction unless a concrete defect is found; those lanes are held.
- Verify every returned lane against scaling, cutoff uniformity, source exhaustiveness, non-circularity and viscosity budget.
- Refine only when at least one load-bearing clause changes state, or when a proposed route is falsified by a quantified counterexample.

The disjoint development lanes are now:

1. Finite-dimensional continuum Galerkin ODE existence and propagation of reality/transversality on the exact carrier.
2. Five physical source estimates uniform in shell and Galerkin cutoffs.
3. Hysteretic positive-variation estimate.
4. Dissipation-wavenumber high-mode condition and low-frequency critical reservoir.
5. Periodic principal-value kernel, sphere integration and Calderón–Zygmund estimates.
6. Continuum filter-increment-to-diffusion coercivity.
7. Uniform residual-tail ratios and strict combined coefficient.
8. Analytic shell/Galerkin convergence, local critical restart, pressure recovery and Galilean invariance.
9. Claimed-paper discovery, source preservation, falsification and crosswalk to lanes 1–8.
10. Documentation, diagrams, change control and verification after substantive lanes return.

## Architecture and verification

- [C4/PlantUML source](architecture.puml)
- [Verification and quality gates](verification.md)
- [Governance and standards alignment](governance.md)
- [Claimed-paper corpus and audits](paper-corpus/README.md)
- [Round 25 physical carrier and support closure](physical-carrier-support-round25.md)

## Scope boundary

Round 25 does not claim global regularity, completed L3 ODE analysis, classwise cutoff-uniform nonlinear taxes, a strict viscosity margin, successful Agda kernel validation, successful GitHub Actions, publication readiness or Clay acceptance. It makes one substantive ladder promotion—L4 to checked exact—and narrows L3 to its genuine analytic remainder.
