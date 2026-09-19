# Yang–Mills exact residual brief — 2026-09-19 frontier reconciliation

## Authority and scope

This is the live bookkeeping surface for PR #996 after the closed-world/min-cut reconciliation.

```text
source authority
!= compiler theorem
!= physical inhabitant
!= empirical contact
```

The top-level frontier remains

[
oxed{F_1+F_3+F_4}.
]

What changed is the location of the primitive cuts.

---

# Paid structure — do not rebuild

The repository already owns substantial machinery for:

- literal finite four-dimensional SU(2) Wilson/Gibbs carriers, plaquettes and action;
- gauge invariance and literal physical Wilson jets/Hessian/coercivity;
- normalized T5 source algebra and exact connected-covariance identities;
- marked-source decay compilers and dense-local -> full-`L2_0` extension;
- finite transfer/form-gap and varying-carrier transport compilers;
- beta-driven same-history complete-density / finite-measure carriers;
- abstract Mosco/recovery -> continuum-gap transport;
- OS reconstruction, Stone uniqueness, local-core cutoff stabilization;
- common-core equality -> equality of self-adjoint generators.

Therefore:

```text
PLAQUETTE/WILSON CONSTRUCTION   != F1
FULL R339 MAGNITUDE EQUALITY   != F1
ABSTRACT MOSCO THEORY         != F3
STONE / GENERATOR UNIQUENESS  != F4
EVOLUTION EQUALITY AS AXIOM   != F4
```

---

# F1 — weakest physical min-cut

The terminal finite-side target remains

[
|langle P_0psi,P_1psiangle|
 le c_k|psi|_2^2,
qquad
Delta a_kle1-c_k.
]

A trajectory-uniform constant `c < 1` is not required.

## R339 recut

`BalabanCMP116R281SelectedSourceUpperRound343Exact` explicitly records

```text
sourceMagnitudeEqualityPrimitiveForMassGapConsumer = false
```

and replaces source/selected magnitude equality by the one-sided selected-response upper actually consumed downstream.

R344 and R346 continue weakening the source interface on the actual shared-marked carrier. Therefore

```text
R339.sourceMagnitudeIsSelectedMagnitude
```

is an obsolete-strength ABI for the mass-gap route, not primitive proof debt.

The new owner

```text
YMClayF1PhysicalMinCutExact
```

records the four physical leaves:

```text
F1-A  actual selected CMP116 localization
      on the canonical physical source carrier

F1-B  literal Wilson local/cylinder observable
      = selected R295/T5 Gibbs observable

F1-C  rooted/source envelope
      <= c_k ||psi||^2_(L2 mu_k)
      on a dense physical vacuum-complement algebra

F1-D  Delta*a_k <= 1-c_k
      on the existing beta-history / literal-Wilson trajectory
```

R403 already makes `SourceDirection = TestObservable` definitionally, so F1-A does not need a new observable-to-J representation theorem.

The WrongType firewall remains explicit: P33 Wilson “correlation” is Hessian/coercivity structure; R295 connected covariance is statistical Gibbs covariance. F1-B is the physical same-object weld between those worlds.

After F1-B/C, the existing route is:

```text
R295
 -> marked-source adapter
 -> connected-correlation bound
 -> dense physical F1 producer
 -> dense-L2 extension
 -> full physical L2_0 decorrelator.
```

---

# F3 — finish the existing Sprint construction program

F3 is not “implement Mosco recovery from scratch.”

The concrete implementation staircase already exists:

```text
Sprint109-110
  recovery/Mosco/common-carrier consumers

Sprint111
  finite <-> continuum embedding/projection surface

Sprint112
  P_a sampling candidate
  E_a renormalized interpolation candidate
  quotient-independence diagrams

Sprint113+
  gauge covariance
  quotient/norm/Jacobian/quadrature estimates

Sprint114-122
  closure criteria, reducers and propagation
```

The new owner

```text
YMClayF3SprintConstructionFrontierExact
```

makes the actual physical inputs explicit:

```text
actual P_a
actual E_a
representative independence + gauge/quotient compatibility
uniform norm + approximate inverse control
residual + strong convergence
energy liminf/limsup recovery
vacuum-sector stability
literal Wilson measure convergence
```

The existing Sprint flags remain fail-closed. In particular:

```text
Sprint112 samplingProjectionMapConstructedHere = false
Sprint112 interpolationMapConstructedHere = false
Sprint116 unconditionalNormWindowTheoremProvedHere = false
Sprint116 quotientGaugeAnalyticFeedsDischargedHere = false
```

Reducer receipts are diagnostic surfaces only and do not inhabit the new physical F3 record.

Once these analytic maps/estimates produce the actual

```text
VacuumOrthogonalRecoverySystem
```

the continuum vacuum-gap theorem is existing compiler output.

The literal finite-measure convergence theorem remains a separate physical leaf on the same beta-driven Wilson family; Round126 stores it and later rounds export it but do not construct it.

---

# F4 — common-core physical data, then compiler output

The primitive F4 boundary is now

```text
YMClayPhysicalStressOSCommonCoreWitnessExact.PhysicalStressOSCommonCoreWitness
```

rather than `YMOSSameObjectWitness.evolutionsEqual`.

Its physical content is:

```text
actual reconstructed common core
actual YM/stress core action
actual OS core action
core-action equality
YM closure / essential-self-adjointness identification
OS closure / essential-self-adjointness identification
```

via the existing

```text
YangMillsStressWardCommonCoreGeneratorExact.StressOSCommonCoreData.
```

The compiler chain is now explicit:

```text
physical StressOSCommonCoreData
  -> commonCoreWardImpliesSameGenerator
  -> same self-adjoint generator
  -> Stone/OS generator-to-evolution bridge
  -> YM evolution = OS evolution
  -> derived YMOSSameObjectWitness
```

Thus evolution equality is no longer a primitive field of `OutstandingPhysicalFrontier`.

The remaining physical work upstream is the continuum stress/Ward construction:

```text
renormalized local stress/current
+ translation Ward identity
+ microcausal/local shell data
+ stabilized local charge action
+ common-core closure identifications.
```

Generic cutoff stabilization, outer-shell elimination, closure equality and Stone uniqueness are already compiler-owned.

---

# Canonical current min-cut

```text
F1
  1. selected CMP116 physical localization
  2. Wilson <-> R295 same-object observable weld
  3. rooted/source shell <-> physical L2 normalization
  4. beta/a trajectory gap calibration

F3
  5. actual P_a sampling map
  6. actual E_a interpolation map
  7. quotient/gauge/norm/approximate-inverse control
  8. strong/residual convergence + energy recovery + vacuum stability
  9. literal Wilson measure convergence

F4
  10. continuum renormalized stress/current Ward data
  11. local-charge stabilization inputs on the reconstructed core
  12. physical YM/OS common-core action + closure identifications
```

Several of these are expected to collapse together under the right physical constructors.

The conceptual status is:

```text
finite Wilson geometry/action/plaquettes          deeply paid
finite physical transfer/gap compilers            paid
source/cumulant/covariance algebra                paid
dense observable -> L2_0 extension                paid
varying-carrier abstract transport                paid
Mosco/recovery abstract theorem                   paid
OS/Stone uniqueness                               paid
common-core equality -> generator equality        paid

same-object physical instantiations               remaining
scale-uniform analytic estimates                  remaining
continuum sampling/interpolation estimates        remaining
continuum stress/Ward identification              remaining
```

## Verification boundary

This reconciliation tranche is source-written only. No exact-head Agda or Lean kernel run was performed in this connector session.

Before promotion:

1. typecheck `YMClayAristotleGapParityEverything.agda` on the exact branch head;
2. build the corresponding Lean tree where relevant;
3. audit for `sorry`, `axiom`, `postulate`, `@[implemented_by]` and unresolved metas;
4. preserve all physical F1/F3/F4 records as conditional until actual inhabitants are constructed.

No status Boolean, source citation or historical receipt is promoted to a physical theorem inhabitant.
