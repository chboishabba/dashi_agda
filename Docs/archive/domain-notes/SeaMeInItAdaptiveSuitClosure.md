# SeaMeInIt adaptive-suit authority closure

## Purpose

`DASHI.Interop.SeaMeInItAdaptiveSuitClosure` extends the physical ROM closure into the actual adaptive-product authority chain:

```text
PhysicalROMValidationReceipt
  -> AdaptiveModuleReceipt
  -> ControllerSafetyReceipt
  -> SuitDeploymentReceipt
```

Each stage has its own promotion gates. No stage receives authority merely because the preceding mathematical structure exists.

## Adaptive modules

`AdaptiveModuleReceipt` depends on a promoted physical-ROM receipt and carries separate gates for module inventory, command envelope, fail-safe evidence, power budget, and evidence provenance.

The intended runtime counterparts are sensors, actuators, power modules, heating/cooling/tensioning modules, and related fail-safe hardware.

Safe reading:

```text
the declared adaptive hardware stack cleared its declared module gates
```

Unsafe reading:

```text
the controller or deployment is therefore safe
```

## Controller safety

`ControllerSafetyReceipt` depends on promoted adaptive hardware and separately gates scenario coverage, hard violations, command latency, emergency stop, and controller evidence.

A latency witness is carried explicitly as:

```text
maxCommandLatency <= commandLatencyThreshold
```

The carrier also records the claim boundary that scenario-relative validation is not universal closed-loop safety.

## Deployment authority

`SuitDeploymentReceipt` depends on a promoted controller but adds a separate:

```text
externalAuthorityReviewGate
```

That gate is deliberately an input. There is no theorem in the module deriving it from physical-ROM promotion, adaptive-module promotion, controller tests, or the C3 transport theorem.

A promoted deployment witness therefore requires:

```text
physical ROM promoted
adaptive module promoted
controller promoted
all deployment gates admissible
external authority review admissible
```

This is the final authority firewall:

```text
proof/test success != automatic permission to deploy on a human or in the field
```

## Full ROM-to-adaptive-suit compiler

The combined SeaMeInIt/DASHI reading is now:

```text
Body / ROM
  -> projected garment fields
  -> seam topology
  -> panel topology
  -> metric correction
  -> pattern serialization
  -> manufacturing
  -> physical assembly
  -> measured wear-fit residual
  -> physical ROM closure
  -> adaptive hardware
  -> controller safety
  -> external deployment review
```

C3/BT369 remains a typed provenance/orientation/refinement transport within this compiler. It does not bypass any empirical or authority gate.
