# Quantum Path Fibre Observation Quotient

Implemented module:

```text
DASHI.Physics.Closure.QuantumPathFibreObservationQuotient
```

This records the fetched thread tail as a bounded observation surface:

```text
admissible path fibres
  -> amplitude / action / phase contribution
  -> phase-sensitive transport
  -> observation quotient
```

It is theorem-thin. The module does not prove quantum electrodynamics,
measurement collapse, retrocausality, or constant-time rendering.

## Common Carrier

`AdmissiblePathFibreCarrier` packages:

- source and detector boundaries,
- path fibres,
- amplitude, action, and phase-contribution carriers,
- admissibility receipts,
- a phase-coupling classifier.

This is the shared carrier for double slit, Feynman/Fermat path-integral
readings, gratings/masks, and quantum eraser quotients.

## Double Slit Surface

`DoubleSlitPhaseSurface` records:

```text
incoming fibre
  -> coherent left/right split
  -> cross-fibre phase coupling
  -> screen interference quotient
```

It also records the which-path quotient:

```text
path fibre
  -> branch quotient
  -> distinguished branch data
```

The distinction is structural: coherent branch mixing and which-path
distinction are different observation quotients over the same path-fibre
carrier.

## Feynman / Fermat Surface

`FeynmanFermatPathSurface` records:

- a list of admissible fibres between boundary data,
- path-integral observation over those fibres,
- stationary-action and stationary-phase attractor predicates,
- a mirror/Fermat path selector,
- grating or mask retopologization of the admissible fibre set,
- cancellation topology after the mask.

This captures the DASHI reading:

```text
many admissible fibres
  -> phase cancellation / reinforcement
  -> stationary attractor in the observed quotient
```

## Quantum Eraser Surface

`QuantumEraserQuotient` records:

```text
signal + idler
  -> entangled pair
  -> one-particle quotient
  -> smudged observation
```

and separately:

```text
entangled pair
  -> joint/coincidence quotient
  -> correlated sub-fibre selection
```

The key boundary is that joint selection is not a future-changes-past claim.
It is a quotient over correlated data.

## Non-Promotion Boundaries

`canonicalQuantumPathBoundaries` blocks:

- future-changes-past promotion,
- classical hidden-path promotion,
- global QED completeness promotion,
- O(1) renderer theorem promotion,
- measurement-collapse theorem promotion,
- retrocausal eraser promotion.

`canonicalQuantumPathNonPromotionCertificate` carries these as false
promotion flags.

## Toy Witness

The module includes toy inhabitants:

- `canonicalAdmissiblePathFibreCarrier`
- `canonicalDoubleSlitPhaseSurface`
- `canonicalFeynmanFermatPathSurface`
- `canonicalQuantumEraserQuotient`
- `canonicalQuantumPathFibreObservationQuotient`
- `canonicalQuantumPathNonPromotionCertificate`

They inhabit the structure without asserting physical completeness.

## Validation

Focused validation command:

```bash
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Physics/Closure/QuantumPathFibreObservationQuotient.agda
```
