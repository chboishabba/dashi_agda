# Yang--Mills Agda / Lean Clay parity — 2026-09-17

Status: theorem-topology parity implementation on `agent/ym-final-direct-upper-closure`.

This document records code ownership. It is not theorem authority and does not promote a conditional physical input.

## New Agda owners

```text
DASHI/Physics/YangMills/YMClayBoundedFormParityExact.agda
DASHI/Physics/YangMills/YMClayMassGapAssemblyParityExact.agda
DASHI/Physics/YangMills/YMClayFullChainParityExact.agda
DASHI/Physics/YangMills/YMClayAgdaParityValidation.agda
```

They mirror the retained Lean `RequestProject.YangMills.Clay` consumer topology without creating a second spectral/clustering theory.

## Bounded-form route

The Agda bounded form package reuses `YMKatoClosedFormHamiltonianExact` as the canonical associated-operator owner.

```text
BoundedFormGapPackage
  -> boundedAssociatedHamiltonian
  -> canonical Kato self-adjoint operator
  -> FiniteVacuumFormGapDatum
```

`FiniteVacuumFormGapDatum` retains the exact physical fields consumed downstream:

```text
normalized vacuum
vacuum-null form datum
vacuum-complement coercive datum
associated self-adjoint operator
```

There is no additional `formGapCompiler` hypothesis in the final parity route.

## Source route

`YMClayFullChainParityExact.directSelectedSourceBuildsMassGapConclusion` is specialized to the current source consumer:

```text
R387.DirectSelectedSpectralUpper
+ R342.SelectedLimitUpperClosure
+ positive selected candidate gap
  -> BalabanDirectSelectedUpperToGapFinalExact
  -> Gap.PositiveTransferGapCore
  -> common cutoff/continuum/OS route
  -> Assembly.MassGapConclusion.
```

Therefore R410 is not reintroduced as terminal architecture.

## Common continuum / OS route

`CommonContinuumOSRoute` is the Agda analogue of Lean `CutoffFamily + OSWeld`:

```text
FiniteGap proof object
  -> cutoffToContinuum
  -> ContinuumGap
  -> ymOSSameObject
  -> MassGapConclusion.
```

The finite proof object remains in `Set₁`; the route is universe-correct in `Set₂` rather than erasing it to a Boolean/status token.

## Final conclusion shape

`MassGapConclusion` records the same endpoint classes as the retained Lean assembly:

```text
positive gap
vacuum form gap
no positive subgap mode
vacuum-sector resolvent conclusion
```

The concrete Hamiltonian, vacuum, and gap parameter remain explicit.

## Physical inputs deliberately not manufactured

The parity compiler does not construct:

```text
literal finite physical Yang--Mills bounded form q_a
literal vacuum-null proof for q_a
literal uniform coercivity for q_a
literal R387 direct selected source upper
actual cutoff->continuum physical graph/closure inhabitant
actual YM/OS same-object evolution/reconstruction inhabitant
```

Those are still the physical producer boundary. The new Agda files ensure that, once supplied, there is no parity gap between the Agda and Lean assembly topologies.

## TDD / verification boundary

The validation owner was committed first at RED (`5c6974af...`) while both production imports were absent. Production owners followed, then the validation surface was tightened to retain `Set₁` proof objects without Boolean erasure.

No exact-head Agda kernel receipt is claimed until an actual Agda run is observed for the feature head.
