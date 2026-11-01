# Quantum Path / Light Transport Promotion-Gated Discharge

Implemented module:

```text
DASHI.Interop.QuantumPathLightTransportAnalogyDischarge
```

This links the quantum path-fibre quotient to renderer light transport as a
promotion-gated surface:

```text
weighted/admissible fibres
  -> cancellation or residual structure
  -> quotient-dependent observation
  -> receipt-gated reuse
```

The canonical discharge does not make the separate `dashiRTX` physically-based
raytracing / MDL sparse light-transport prototype part of DASHI Agda, a QED
implementation, scaffolding for the adelic Sobolev bridge, a renderer algorithm
derived from quantum optics, or a global exact `O(1)` rendering theorem.  It
records only a DASHI-internal analogy surface that would require the receipts
below before any stronger renderer-facing claim could be reused.

Current fail-closed guards:

- quantum path as renderer algorithm;
- renderer closure as QED proof;
- retrocausal renderer claims;
- global `O(1)` physical exactness;
- hidden residual or side-information discard;
- measurement-collapse theorem promotion.

Promotion requirements:

- path-integral to closed-transport compiler;
- stationary-phase error bound;
- material scattering law receipt;
- visibility/mask completeness receipt;
- residual tolerance proof;
- side-information budget proof;
- renderer runtime-complexity proof;
- empirical renderer conformance receipt.

`PromotedQuantumPathLightTransport` is the promoted form. It requires a
`QuantumLightTransportPromotionReceipt`, so the stronger renderer/QED-backed
transport claim is no longer excluded by the formalism, but it is still
receipt-gated.

First inhabited subset:

```text
DASHI.Interop.StationaryPhaseMirrorGratingToyReceipt
```

This covers the stationary-phase mirror/grating toy lane only:

```text
known optical setup
  -> path-fibre compiler
  -> masked/grating closure
  -> predicted intensity
  -> analytic reference comparison
  -> residual bound
```

It discharges the compiler/error/mask/residual subset while leaving the full
promotion receipt uninhabited.

Focused validation:

```bash
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Interop/QuantumPathLightTransportAnalogyDischarge.agda
```
