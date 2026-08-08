# Navier–Stokes Clay contract

This directory is the normalized entry point for the periodic Navier–Stokes Clay route.

## Current answer

### Is the true Clay requirement represented?

Yes. Round 23 added a literal formal target for Fefferman’s periodic alternative B, including positive viscosity, three dimensions, zero forcing, smooth divergence-free periodic initial data, global smooth velocity and pressure, and the pressure-periodicity erratum.

Mean zero is not a Clay precondition. It is a reduction handled by a separate centering and Galilean-restoration theorem. Uniqueness and a separate energy-equality condition are not inserted into the official target.

### Is there a single in-repository path?

Yes. The terminal composition is present. The remaining work is not another theorem wrapper; it is inhabiting the physical analytic producers:

1. construct the literal finite Galerkin flow;
2. derive its filtered-vorticity shell balance;
3. prove cutoff-uniform taxes for every physical source;
4. obtain one strict viscosity margin;
5. pass shell and Galerkin cutoffs;
6. derive critical/Serrin continuation;
7. recover smooth periodic pressure;
8. restore arbitrary periodic mean and inhabit the literal target.

The dependency-ordered version is the [highest-alpha lemma ladder](paper-corpus/highest-alpha-lemma-ladder.md).

## Implemented rounds

### Round 24 — claimed-paper corpus and audits

The [claimed-paper corpus](paper-corpus/README.md) includes peer-reviewed, arXiv, repository, independent and web claims. Sources enter only at their first load-bearing lemma. Valid local results are retained even when a terminal implication fails, and exact countermodels document recurrent failure modes.

### Round 25 — literal physical carrier and support

The [physical carrier and support tranche](physical-carrier-support-round25.md) proves:

- complete duplicate-free physical output fibres;
- low–low-to-far-high exclusion;
- exhaustive and unique `HH/LH/HL/CC` triad classification;
- a separate differentiated `Com` source;
- exact `HH+LH+HL+CC+Com` recomposition with no generic remainder.

### Round 26 — signed critical ledger and unique tax ownership

The [finite Galerkin and critical-tax tranche](galerkin-critical-ledger-round26.md) proves:

- degree-two Galerkin coordinate syntax and exact finite difference factorisation;
- reality reconstruction and conjugate transversality;
- physical triad-energy cancellation;
- a signed weighted critical shell ledger;
- a bridge forcing literal physical sources into the shell ledger;
- low-transport cancellation and finite signed commutator identities;
- division-free high–high normalisation;
- hysteretic entry charge;
- named remainder classes;
- duplicate-free tax ownership.

It does not prove finite Picard–Lindelöf, the physical time-dependent shell balance, cutoff-uniform taxes or a strict viscosity margin.

### Round 27 — projectors, operators, centred probes and maximal core

The [projector/operator/core tranche](projector-operator-core-round27.md) imports useful finite harmonic-analysis architecture from the Monster projector lane without asserting a physical relationship between the subjects. It proves:

- sharp finite shell-projector idempotence, disjointness and resolution;
- shell covariance and diagonal multiplier commutation;
- Fourier reality as the fixed-point set of an involution;
- a generic equivariant-vector-field preservation theorem;
- diagonal multiplier reality equivariance;
- distinct state and multiplier/test carriers;
- the exact signed translation–multiplier commutator;
- the division-free centred five-source probe identity;
- a maximal common viscosity-core theorem under exact owner reconstructions;
- physical-triad Plücker/Gram geometry;
- a reproducible finite certificate pipeline.

These are exact mathematical lemmas. They do not supply the full nonlinear vector-field equivariance, finite ODE theorem, physical source estimates or strict coefficient below one.

### Round 28 — dependent carrier, signed constituent and owner-partition architecture

The [physical-carrier and signed-partition tranche](physical-carrier-partition-round28.md) proves:

- idempotence of the composite of three commuting physical selectors;
- a dependent carrier fixed by Leray, Fourier reality and centering;
- cutoff closure and opposite-output representatives under triad conjugation;
- simultaneous-conjugation invariance of Plücker coordinates and area;
- a signed constituent tree with source-to-owner compatibility;
- delayed positive taxation after owner-homogeneous grouping;
- a dependent unique-owner partition preserving signed and taxable totals;
- signed commutator identities over structured finite interaction fibres;
- exact orbit parity and division-free Plücker homogeneity;
- a no-hidden-norm owner-estimate language;
- exact nine-owner absorption algebra once physical estimates are supplied.

It does not instantiate the concrete physical selector, prove the nonlinear convolution equivariant, produce a cutoff-uniform operator estimate, or prove the strict total viscosity margin.

## Preconditions, postconditions and invariants

The normalized contract is in [requirements.md](requirements.md) and formalized by `NSTriadKNLuoClayPrePostInvariantContractRound23Exact.agda`.

Every load-bearing physical estimate must preserve:

```text
uniformity in shell q, shell cutoff Q, Galerkin cutoff N and finite T*;
critical Navier–Stokes scaling;
full source exhaustiveness;
unique tax ownership;
no uncontrolled target critical norm, BKM norm or Serrin norm on the right;
no assumed alignment, small data or finite residence;
absorption before weak limits;
strict total viscosity coefficient below one.
```

## ZKP orchestration frame

- **O — Organization:** `DASHI/Physics/Closure`, paper-facing interfaces, validation scripts and this documentation surface.
- **R — Requirement:** literal Fefferman periodic alternative B.
- **C — Code:** Rounds 23–28 target, corpus, physical support, signed ledger, projectors, operators, geometry, dependent carriers and tax accounting.
- **S — State:** exact target and extensive finite algebra are implemented; the cutoff-uniform physical absorption theorem is uninhabited.
- **L — Lattice:** finite flow → physical shell ledger → unique source taxes → strict absorption → limits → Serrin continuation → smooth global witness.
- **P — Proposal:** advance only physical producers, exact supporting lemmas, or quantified falsifications.
- **G — Goal:** inhabit the literal periodic theorem for every positive viscosity and smooth divergence-free periodic datum.
- **F — Gap function:** open physical producers weighted first by scaling correctness, cutoff uniformity and strict viscosity margin.

## Active, non-overlapping lanes

1. Instantiate the concrete Leray/reality/centering selector and prove full nonlinear equivariance.
2. Finite normed local Lipschitz, Picard–Lindelöf, energy identity and global finite existence.
3. Physical time-dependent signed constituent shell balance using the sharp projectors.
4. Signed interaction-fibre `TT*` or almost-orthogonality estimate and first uniform class tax.
5. Periodic principal-value strain kernel and Calderón–Zygmund bounds.
6. Division-free directional high–high estimate and defect evolution.
7. Positive-variation and bad-excursion amplitude budgets.
8. Lower interaction, far-field, commutator and cutoff-tail taxes.
9. Physical nine-owner estimates and strict viscosity margin.
10. Shell/Galerkin compactness, critical-to-Serrin continuation, pressure and Galilean recovery.
11. Claimed-paper discovery and falsification mapped to lanes 1–10.
12. Documentation and verification only after substantive mathematical changes.

Terminal composition is held unless a concrete defect is found.

## Architecture and verification

- [C4/PlantUML source](architecture.puml)
- [Verification and quality gates](verification.md)
- [Governance and standards alignment](governance.md)
- [Claimed-paper corpus and audits](paper-corpus/README.md)
- [Round 25 physical carrier and support](physical-carrier-support-round25.md)
- [Round 26 finite Galerkin and critical-tax ledger](galerkin-critical-ledger-round26.md)
- [Round 27 projector/operator/core tranche](projector-operator-core-round27.md)
- [Round 28 physical carrier and signed partition](physical-carrier-partition-round28.md)

## Scope boundary

Round 28 does not claim:

- global regularity;
- a concrete physical selector instance;
- full nonlinear Fourier-reality equivariance;
- a completed finite Picard–Lindelöf instance;
- a physical time-dependent shell balance;
- smooth Littlewood–Paley bounds;
- any cutoff-uniform nonlinear tax;
- the periodic singular-kernel estimate;
- physical nine-owner estimates;
- a strict total coefficient below one;
- successful shell/Galerkin limits;
- successful Agda kernel validation or GitHub Actions;
- publication readiness or Clay acceptance.

The current highest-value target remains `UniformCriticalNonlinearityAbsorption`, with a cutoff-independent coefficient strictly below one.
