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

Round 25 closes the discrete support part of that path. The [literal physical carrier and five-class support tranche](physical-carrier-support-round25.md) proves duplicate-free output fibres, the low-low-to-far-high obstruction, exhaustive and unique physical triad classification, and exact `HH+LH+HL+CC+Com` recomposition after evaluating the appended `Com` cell with a mode-indexed commutator functional. L4 is checked exact; L3 is narrowed to finite-dimensional continuum ODE existence and constraint propagation.

Round 26 adds the [finite Galerkin and critical-tax tranche](galerkin-critical-ledger-round26.md). It proves a literal degree-two coordinate algebra, exact triadwise energy cancellation, a signed weighted critical shell ledger, the finite kernel-commutator identity and first-moment scaling, division-free high–high normalization, hysteretic positive-variation charge, named remainder classes and duplicate-free tax ownership. These advances constrain how the remaining estimates may be proved; they do not supply cutoff-independent analytic coefficients.

### 3. What are the preconditions, postconditions and invariants?

They are defined in [requirements.md](requirements.md) and formalized by `NSTriadKNLuoClayPrePostInvariantContractRound23Exact.agda`.

The dependency-ordered statement of the remaining mathematics is in the [highest-alpha lemma ladder](paper-corpus/highest-alpha-lemma-ladder.md).

## ZKP orchestration frame

- **O — Organization:** `DASHI/Physics/Closure`, the paper-facing theorem interfaces, validation scripts and this documentation surface.
- **R — Requirement:** Fefferman periodic alternative (B), including the pressure-periodicity erratum.
- **C — Code:** Round 22 finite Galerkin and defect modules; Round 23 literal contract, adapter and Galilean reduction; Round 24 claimed-paper corpus and normalized ladder; Round 25 literal carrier certificate and physical support closure; Round 26 finite Galerkin cancellation, signed critical ledger and tax ownership.
- **S — State:** theorem type, terminal reducers, L4 physical support, finite triad cancellation and tax-partition algebra implemented; the physical theorem remains uninhabited.
- **L — Lattice:** finite PDE → signed critical ledger → duplicate-free physical taxes → strict absorption → nested limits → restart → smooth global witness → literal Clay witness.
- **P — Proposal:** work only on physical producers that move a clause from `physicalProducerOpen` to `checkedExact`/`checkedReducer`, or source audits that rigorously falsify a proposed producer.
- **G — Goal:** inhabit the literal periodic Fefferman statement for every positive viscosity and every smooth divergence-free periodic datum.
- **F — Gap function:** count of load-bearing open producers, weighted first by scaling correctness, then cutoff uniformity, then strict viscosity margin.

## Updated plan and roadmap

The target theorem is literal, mean zero is a reduction rather than a Clay precondition, physical support is tied to the actual cutoff `Z³` carrier, and tax ownership is explicit.

- Frame all further work around the literal periodic Fefferman statement.
- Search broadly, including unconventional, unreviewed and incorrect papers.
- Preserve valid local lemmas even when a terminal proof fails.
- Keep exact signed identities separate from positive-production taxes.
- Assign every taxable atom and every remainder exactly once.
- Keep one non-overlapping lane for each open physical producer.
- Do not assign work to terminal composition, nested-limit logic or restart contradiction unless a concrete defect is found; those lanes are held.
- Verify every returned lane against scaling, cutoff uniformity, source exhaustiveness, non-circularity, duplicate ownership and viscosity budget.
- Refine only when at least one load-bearing clause changes state, or when a proposed route is falsified by a quantified counterexample.

The disjoint development lanes are now:

1. Concrete continuum-real Galerkin ODE existence, conjugate transversality and global finite existence.
2. Physical derivation of the signed critical shell ledger from the literal Galerkin solution.
3. Low-advection finite-kernel commutator estimate and first cutoff-independent class tax.
4. Hysteretic positive-variation PDE estimate and bad-excursion amplitude budget.
5. Dissipation-wavenumber high-mode condition and low-frequency critical reservoir.
6. Periodic principal-value kernel, sphere integration and Calderón–Zygmund estimates.
7. Continuum filter-increment-to-diffusion coercivity and division-free high–high tax.
8. Uniform residual-tail ratios and strict combined coefficient.
9. Analytic shell/Galerkin convergence, local critical restart, pressure recovery and Galilean invariance.
10. Claimed-paper discovery, source preservation, falsification and crosswalk to lanes 1–9.
11. Documentation, diagrams, change control and verification after substantive lanes return.

## Architecture and verification

- [C4/PlantUML source](architecture.puml)
- [Verification and quality gates](verification.md)
- [Governance and standards alignment](governance.md)
- [Claimed-paper corpus and audits](paper-corpus/README.md)
- [Round 25 physical carrier and support closure](physical-carrier-support-round25.md)
- [Round 26 finite Galerkin and critical-tax ledger](galerkin-critical-ledger-round26.md)

## Scope boundary

Round 26 does not claim global regularity, a completed continuum-real L3 ODE instance, classwise cutoff-uniform nonlinear taxes, a strict viscosity margin, successful Agda kernel validation, successful GitHub Actions, publication readiness or Clay acceptance. It proves finite algebra and accounting needed to make later analytic failures localizable: triadwise cancellation, signed critical recomposition, finite commutator increments, division-free HH normalization, positive-variation entry charge, named remainders and duplicate-free tax ownership.
