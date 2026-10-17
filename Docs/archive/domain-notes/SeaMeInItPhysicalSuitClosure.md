# SeaMeInIt physical suit closure

## Purpose

`DASHI.Interop.SeaMeInItPhysicalSuitClosure` extends the existing SeaMeInIt receipt surface past the digital finished-pattern boundary.

The typed order is:

```text
FinishedSeamReceipt
  -> AssemblyReceipt
  -> WearFitReceipt
  -> PhysicalROMValidationReceipt
```

This is intentionally not a proof that a manufactured garment is safe, comfortable, clinically effective, or physically correct. It is a proof-oriented receipt surface that prevents the digital pattern artifact from being silently promoted into physical authority.

## Assembly receipt

The assembly layer binds the promoted finished pattern to a physical realization using:

```text
finished pattern receipt hash
manufactured artifacts hash
assembled geometry hash
assembly evidence hash
material lot hashes
piece count
realized seam count
measured geometry deviation
geometry deviation threshold
```

The Agda carrier requires an explicit proof that the upstream `FinishedSeamReceipt` is promoted and carries a witness that the declared geometry deviation is within threshold. The remaining realization/provenance checks remain tri-valued gates.

## Wear-fit receipt

The wear-fit layer binds an assembly to a declared ROM/task validation slice. Residual channels carry a channel name, residual, threshold, a proof that the residual is within threshold, and a tri-valued gate.

The intended physical interpretation is predicted-vs-measured pressure/shear/support/tension/clearance/thermal behavior, but the formal carrier remains sensor-agnostic.

## C3 / BT369 transport

The physical closure imports the repo's exact finite C3 action from:

```text
DASHI.Core.FiniteC3OrbitStabilizerExact
```

`C3BT369TransportWitness` requires a transport map

```text
transportPhase : C3 -> C3
```

and the exact equivariance law

```text
transportPhase (g . x) = g . transportPhase x
```

for every `g,x : C3`.

This is a law of the declared symbolic transport, not a claim that cloth mechanics themselves have exact C3 symmetry. The record therefore also carries a separate `transportEvidenceGate`. `identityC3TransportDiagnostic` proves that the mathematical contract is inhabited while deliberately leaving that empirical gate diagnostic.

This split is the intended firewall:

```text
exact symbolic transport law
!=
measured physical transport evidence
```

The runtime SeaMeInIt companion records a numerical `c3_equivariance_error` and threshold, plus phase/address/orientation provenance. Missing required transport evidence is diagnostic; measured error above threshold rejects.

## Physical ROM validation

`PhysicalROMValidationReceipt` binds the promoted wear-fit receipt back to the source ROM and optional calibrated ROM. Strict physical gates cover physical evidence, residual closure, C3 transport, calibration, and claim boundary.

Promotion therefore means only:

```text
the declared physical validation slice closes under every required receipt gate
```

It does not mean:

```text
universal garment physics
clinical safety
automatic deployment authority
```

## End-to-end compiler reading

`ROMToSuitClosureSurface` exposes the full object order:

```text
Body
ROM
Field
Seam
Panel
Pattern
Assembly
WearMeasurement
PhysicalROM
```

with receipt-labelled morphisms between each stage and an explicit C3 address-transport receipt.

This is the strongest current interpretation of the SeaMeInIt/DASHI integration: C3 is used as a provenance-preserving transport/refinement contract inside the ROM-to-suit compiler, not as a free-standing physical numerology claim.
