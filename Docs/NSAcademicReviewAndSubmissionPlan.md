# Navier–Stokes academic review and submission plan

## Present status

The repository now has a machine-checked implication architecture from the compact-Γ analytic cutset to finite vorticity expenditure and BKM continuation. It also has concrete theorem-facing owners for:

- cutoff-uniform shell/Schur analysis;
- far-low commutator and far-tail decay;
- Galerkin compactness and nonlinear-limit identification;
- invariant-region and barrier-domain control;
- exact packet, Γ-floor, and off-packet reserve formulas;
- inequality-native differential expenditure;
- Bernstein-weighted vorticity reconstruction;
- an explicit analytic cutset adapter;
- a fail-closed submission-readiness gate.

This is not yet a proof of global regularity. The remaining work is the construction of inhabitants for the hard analytic records, followed by a complete human-readable proof and independent specialist review.

## The mathematical cutset

A complete proof branch must contain actual inhabitants, in one fixed periodic 3D Navier–Stokes carrier, of all of the following.

1. **Quantitative full-shell estimate**
   - explicit shell cardinality and weighted convolution constants;
   - cutoff-independent Schur row and column bounds;
   - compatibility with the canonical differentiated triad kernel.

2. **Γ-floor differential inequality**
   - numerator chain rule along the Navier–Stokes time derivative;
   - exact near/far decomposition;
   - near-shell Schur estimate with constants;
   - far-tail decay with a radius chosen uniformly in shell and cutoff;
   - quotient and logarithmic chain rules under invariant-region positivity;
   - identification of a nonnegative coercive envelope dominating the weighted shell rate.

3. **Off-packet differential inequality**
   - exact off-packet shell sum;
   - internal transfer cancellation and boundary flux identity;
   - remote viscous damping;
   - near-shell and far-tail controls;
   - denominator lower bound and selected barrier chain rule;
   - a nonnegative off-packet coercive contribution.

4. **Five-halves shell decay**
   - shell curl and Bernstein estimates;
   - Littlewood–Paley reconstruction;
   - a uniform summable coefficient family around the active packet;
   - Tonelli/monotone-convergence passage through time;
   - normalization of the coefficient constant into the coercive envelope.

5. **Real integration**
   - absolute continuity of the potential;
   - integrability of coercive, dissipation, and forcing rates;
   - a.e. pointwise inequality;
   - fundamental theorem, integral congruence, linearity, and monotonicity;
   - the exact endpoint inequality consumed by the Route-B producer.

6. **Solution-class closure**
   - finite-dimensional Galerkin energy equality;
   - cutoff-uniform energy and time-derivative estimates;
   - Aubin–Lions extraction;
   - nonlinear-limit identification;
   - lower semicontinuity;
   - weak–strong uniqueness or another precise identification with the selected path.

## Highest-alpha research order

The recommended order is:

1. prove or disprove the proposed five-halves shell-decay estimate in ordinary mathematics;
2. derive the Γ-floor differential inequality with every constant visible;
3. derive the off-packet inequality and verify that its sign is compatible with the same potential;
4. test whether one common parameter choice makes the invariant region, tail absorption, and expenditure coercivity simultaneous;
5. only then finish the real-analysis and Galerkin library instantiations.

This order is chosen because failure of items 1–4 would invalidate the claimed global mechanism, whereas items 5–6 are largely standard formalization once the central inequalities are correct.

## Falsification-first checks

Before approaching a journal with a claimed proof, obtain independent answers to these questions.

- Does compact-Γ admissibility actually imply the proposed `2^(5j/2)` shell envelope for every shell, or only for a restricted profile class?
- Is the admissible class preserved for arbitrary smooth finite-energy initial data, or only for data already satisfying a packet concentration hypothesis?
- Can the active shell `K` be chosen consistently through time without discontinuous switching or loss of absolute continuity?
- Is the Γ numerator sign-definite and strictly positive on the entire claimed class?
- Are the Schur and tail constants uniform as the Galerkin cutoff tends to infinity?
- Does any estimate use an `H^s`, vorticity, or continuation bound that is itself downstream of BKM?
- Is the forcing/data remainder finite for arbitrary data in the official problem class?
- Does the final theorem prove the official periodic or whole-space problem, rather than a narrower conditional theorem?

A negative answer should produce a precise conditional theorem or counterexample to the proposed mechanism, not be hidden behind a record field.

## Academic review packet

Prepare four artifacts.

### A. Two-page claim map

- exact theorem statement;
- domain and normalization;
- the five decisive inequalities;
- one dependency diagram;
- explicit list of assumptions and postulates;
- exact current status: proved, conditional, computational, or planned.

### B. Core manuscript

Aim initially for 25–50 pages, not a repository dump. It should contain:

- classical preliminaries and relation to BKM/Leray–Hopf/Littlewood–Paley methods;
- exact compact-Γ definition and motivation;
- all constants and quantifiers;
- proofs of the five decisive inequalities;
- invariant-region theorem;
- Galerkin limit;
- non-circular expenditure theorem;
- official-problem corollary;
- limitations and failure modes.

### C. Formal-verification appendix

- pinned Agda and standard-library revisions;
- one aggregate theorem importing the entire proof;
- axiom/postulate audit;
- mapping from each manuscript lemma to an Agda theorem;
- reproducible build instructions;
- distinction between executable diagnostics and kernel proofs.

### D. Reviewer guide

For each decisive lemma, state:

- why it is new;
- where each constant comes from;
- which earlier result is closest;
- the most likely failure mode;
- a minimal standalone statement an analyst can check without learning DASHI or Agda.

## Contact sequence

1. Re-contact the applied-mathematics professor previously approached, but send the two-page claim map and ask for critique of one specific inequality rather than endorsement of a Millennium solution.
2. Seek a harmonic analyst or PDE analyst with Littlewood–Paley/Navier–Stokes expertise to audit the five-halves shell-decay and Γ coercivity steps.
3. Seek a separate expert in weak solutions/Galerkin compactness to audit the limit passage and solution-class match.
4. Seek an Agda/formal-analysis reviewer only after the ordinary mathematical proof has survived the first two audits.
5. Post a preprint only when the hard cutset is fully inhabited and the manuscript theorem matches the formal aggregate.
6. Submit to a reputable PDE/analysis journal or other qualifying mathematical outlet; do not send a proposed solution directly to the Clay Mathematics Institute.

## Promotion policy

Use these labels consistently:

- **architecture complete**: implication graph typechecks;
- **conditional theorem complete**: the theorem follows from explicit analytic hypotheses;
- **analytic cutset inhabited**: every hard hypothesis is proved in the selected carrier;
- **kernel theorem complete**: the official statement follows without hidden assumptions;
- **manuscript ready**: human proof, literature comparison, and axiom audit are complete;
- **submission ready**: specialist pre-review has found no unresolved central objection;
- **community accepted**: independent publication and sustained expert acceptance have occurred.

No earlier label implies a later one.
