# Navier–Stokes Clay contract

This directory is the normalized entry point for the periodic Navier–Stokes Clay route.

## Current answer

The exact Fefferman periodic alternative B is represented literally. Positive viscosity, three dimensions, zero forcing, smooth divergence-free periodic data, global smooth velocity and pressure, both periodicity clauses, incompressibility and initial trace are distinct target fields.

Mean zero is not a Clay hypothesis. It is handled by centering and Galilean restoration. Uniqueness and a separate energy-equality premise are not inserted into the official target.

The terminal composition already exists. The remaining work is the physical analysis:

```text
same-object finite physical flow
-> literal trajectory shell balance
-> nine cutoff-uniform owner estimates
-> strict eta_total < 1
-> shell/Galerkin limits
-> critical-to-Serrin continuation
-> smooth pressure and arbitrary-mean restoration
-> literal Fefferman witness.
```

The dependency-ordered statement is the [highest-alpha lemma ladder](paper-corpus/highest-alpha-lemma-ladder.md).

## Implemented mathematical rounds

### Round 23 — exact target and terminal composition

- literal periodic Fefferman target;
- mean-zero/Galilean reduction;
- legacy-to-literal adapter;
- end-to-end terminal composition;
- fail-closed precondition, postcondition and invariant contract.

### Round 24 — claimed-paper corpus and audits

The [paper corpus](paper-corpus/README.md) keeps source authority separate from claimed conclusions. Exact countermodels cover additive energy floors, finite-horizon versus uniform bounds, nondecaying cascade flux and restricted-class versus universal scope.

### Round 25 — literal physical support

[Round 25](physical-carrier-support-round25.md) proves duplicate-free physical output fibres, low–low/far-high exclusion, unique `HH/LH/HL/CC` classification, separate differentiated `Com`, and exact five-source recomposition.

### Round 26 — signed critical ledger and ownership

[Round 26](galerkin-critical-ledger-round26.md) adds degree-two Galerkin syntax, reality reconstruction, conjugate transversality, triad-energy cancellation, a signed weighted shell ledger, exact source-coordinate forcing, low-transport cancellation, division-free high–high normalization, hysteretic entry charge and duplicate-free tax ownership.

### Round 27 — projector and operator geometry

[Round 27](projector-operator-core-round27.md) adds sharp shell projectors, Fourier-reality involution, typed state/dual carriers, the signed translation–multiplier commutator, centred five-source probes, maximal common-core algebra, Plücker geometry and generated finite certificates.

### Round 28 — dependent selector and admissible taxes

[Round 28](physical-carrier-partition-round28.md) adds the generic commuting physical selector, opposite-output conjugate fibres, finite rational coordinate local-Lipschitz majorants, signed constituent trees, dependent owner partitions, structured signed interaction fibres, orbit parity, division-free defect scaling, a no-hidden-continuation-norm estimate language and exact nine-owner absorption algebra.

### Round 29 — dependent physical flow and falsifiable owner analysis

[Round 29 dependent flow and owner analysis](dependent-flow-owner-analysis-round29.md) adds:

- a concrete reconstructed state space with intrinsic transversality, reality reconstruction and zero-mode exclusion;
- a dependent physical ODE carrier;
- a finite blowup-alternative/energy-control reducer;
- one global bilinear pairing deriving all five physical sources;
- explicit delayed positive taxation and a named lossy fallback;
- integration of the finite cutoff-independent commutator coefficient;
- exact discrete multiplier telescoping;
- a signed cross-shell almost-orthogonality scalar core;
- a scale-normalised bad-amplitude homogeneity theorem;
- a falsifiable `HH-bad` feasibility/no-go criterion;
- symbolic affine owner-cost optimization;
- boundary atoms classified by their limit mechanism;
- negative-norm compactness targets and quantitative critical-to-Serrin algebra.

### Round 30 — literal finite Galerkin coefficient and flow reducers

[Round 30 concrete field](physical-galerkin-concrete-round30.md) and [flow/energy/operator reducers](physical-galerkin-flow-round30.md) add:

- direct transversality and idempotence of the literal Leray projector;
- the exhaustive projected quadratic coefficient;
- the concrete viscous-plus-quadratic dependent vector field;
- finite physical-coordinate, Picard–Lindelöf, energy, global-flow and time-dependent-shell interfaces;
- two-sided operator-valued Cotlar–Stein input and cutoff-uniform row-mass reducers.

The remaining finite seam is not preservation of an abstract carrier. It is the same-object lookup proving that the system velocity and retained modes are literally those stored and reconstructed by the input physical state.

### Round 31 — exact HH-bad inverse-scale mechanism

[Round 31](ns-hhbad-scale-gain-round31.md) proves the sharp scalar absorption mechanism

```text
badOccupation * shellScale <= eta * viscosity
```

implies

```text
badOccupation * shellScale^3 * shellEnergy
  <= eta * viscosity * shellScale^2 * shellEnergy.
```

It also proves the exact critical-occupation identity, the alternative viscous-amplitude absorption route, strengthens the Galerkin builder with the same-carrier/same-object equalities, and compiles a structural anti-circular remainder grammar to the existing owner language.

Round 31 does not produce the physical occupation-time or dissipation-wavenumber estimate. It identifies exactly the one inverse shell scale that the PDE analysis must supply.

## Load-bearing invariant

Every owner estimate must have exactly the shape

```text
positiveProduction_i
  <= eta_i * dissipation
     + A_i(T,u0,nu)
     + B_i(u0,nu) * integralCritical.
```

The structural remainder grammar has no constructor for an uncontrolled target supremum, BKM integral, Serrin norm, alignment assumption or finite-residence assumption.

Every positive constituent has one owner:

```text
HH-good, HH-bad, LH, HL, CC, Com, kernel, tail, boundary.
```

The decisive theorem is

```text
eta_total
 = eta_HH-good + eta_HH-bad + eta_LH + eta_HL + eta_CC
   + eta_Com + eta_kernel + eta_tail + eta_boundary
 < 1.
```

A robust physical proof should expose a positive reserve `delta_NS = 1 - eta_total`, rather than merely approach equality.

## Active highest-alpha lanes

1. Construct the canonical same-object state lookup and instantiate the physical real-coordinate/Picard–Lindelöf bridge.
2. Identify the literal three-leg packets with the same convolution and instantiate real time integration.
3. Construct the literal trajectory shell terms and cutoff boundaries.
4. Prove operator-valued cross-shell almost orthogonality and the first physical `Com` tax.
5. Prove the physical `HH-bad` inverse-scale occupation or viscous-amplitude estimate; refute the route if no cutoff-uniform small coefficient exists.
6. Construct the periodic strain kernel, Calderón–Zygmund bounds and `HH-good` geometric-depletion estimate.
7. Close `LH`, `HL`, `CC`, kernel, tail and boundary owners.
8. Construct one physical nine-owner family with an explicit positive `delta_NS`.
9. Pass shell and Galerkin cutoffs using a physical negative-Sobolev time-derivative bound and Aubin–Lions–Simon compactness.
10. Instantiate periodic Serrin continuation, smooth pressure and Galilean restoration.

No additional terminal wrapper is needed unless a concrete defect is found in the existing composition.

## Architecture and verification

- [C4/PlantUML source](architecture.puml)
- [Verification and quality gates](verification.md)
- [Governance and standards alignment](governance.md)
- [Claimed-paper corpus](paper-corpus/README.md)
- [Highest-alpha ladder](paper-corpus/highest-alpha-lemma-ladder.md)
- [Round 25](physical-carrier-support-round25.md)
- [Round 26](galerkin-critical-ledger-round26.md)
- [Round 27](projector-operator-core-round27.md)
- [Round 28](physical-carrier-partition-round28.md)
- [Round 29 dependent flow and owner analysis](dependent-flow-owner-analysis-round29.md)
- [Round 30 concrete field](physical-galerkin-concrete-round30.md)
- [Round 30 flow and operator reducers](physical-galerkin-flow-round30.md)
- [Round 31 HH-bad scale gain](ns-hhbad-scale-gain-round31.md)

## Scope boundary

The current branch does not claim:

- a canonical same-object physical Galerkin lookup;
- a completed real Picard–Lindelöf or time-integration instance;
- a literal physical time-dependent shell trajectory;
- physical operator-valued cutoff-uniform `TT*`/Cotlar–Stein decay;
- periodic singular-kernel/CZ estimates;
- a physical `HH-bad` occupation/amplitude gain;
- physical good/bad high–high or lower-interaction owner estimates;
- a physical nine-owner budget or positive viscosity reserve;
- successful shell/Galerkin limits;
- periodic Serrin continuation;
- unconditional periodic Navier–Stokes regularity;
- successful Agda-kernel or GitHub Actions validation until observed;
- publication readiness or Clay consideration.

The highest-value frontier remains a physical `UniformCriticalNonlinearityAbsorption` theorem with constants uniform in all cutoffs and a strictly positive viscosity reserve.
