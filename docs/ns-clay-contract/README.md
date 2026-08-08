# Navier–Stokes Clay contract

This directory is the normalized entry point for the periodic Navier–Stokes Clay route.

## Current answer

The exact Fefferman periodic alternative B is represented literally. Positive viscosity, three dimensions, zero forcing, smooth divergence-free periodic data, global smooth velocity and pressure, both periodicity clauses, incompressibility and initial trace are distinct target fields.

Mean zero is not a Clay hypothesis. It is handled by centering and Galilean restoration. Uniqueness and a separate energy-equality premise are not inserted into the official target.

The terminal composition already exists. The remaining work is the physical analysis:

```text
finite physical flow
-> signed filtered-vorticity shell balance
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

Round 29 does not claim that the full Galerkin vector field preserves the reconstructed state, that Picard–Lindelöf has been instantiated, or that any physical cutoff-uniform owner estimate has been proved.

## Load-bearing invariant

Every owner estimate must have exactly the shape

```text
positiveProduction_i
  <= eta_i * dissipation
     + A_i(T,u0,nu)
     + B_i(u0,nu) * integralCritical.
```

There is no constructor for an uncontrolled target supremum, BKM integral, Serrin norm, alignment assumption or finite-residence assumption.

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

## Active highest-alpha lanes

1. Prove literal nonlinear conjugation and full reconstructed-state invariance.
2. Transfer coordinate local-Lipschitz bounds to the real finite norm; instantiate Picard–Lindelöf, energy identity and global finite flow.
3. Derive the time-dependent physical shell balance and classified boundary atoms.
4. Prove operator-valued cross-shell almost orthogonality and the first physical `Com` tax.
5. Construct the periodic strain kernel from its Fourier multiplier and prove Calderón–Zygmund bounds.
6. Close `HH-good`; derive defect evolution and either close or refute the current `HH-bad` parameter family.
7. Close `LH`, `HL`, `CC`, kernel, tail and boundary owners.
8. Select one exact symbolic nine-owner budget with `eta_total<1`.
9. Pass shell and Galerkin cutoffs using an explicit negative-Sobolev time-derivative bound and Aubin–Lions–Simon compactness.
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

## Scope boundary

The current branch does not claim:

- full nonlinear Fourier-reality equivariance;
- a completed real Picard–Lindelöf instance;
- a global finite physical Galerkin trajectory;
- a physical time-dependent shell balance;
- operator-valued cutoff-uniform `TT*`/Cotlar–Stein;
- periodic singular-kernel/CZ estimates;
- physical good/bad high–high or lower-interaction estimates;
- a physical symbolic nine-owner budget;
- a strict physical coefficient below one;
- successful shell/Galerkin limits;
- periodic Serrin continuation;
- unconditional periodic Navier–Stokes regularity;
- successful Agda-kernel or GitHub Actions validation until observed;
- publication readiness or Clay consideration.

The highest-value frontier remains `UniformCriticalNonlinearityAbsorption` with a cutoff-independent physical coefficient strictly below one.
