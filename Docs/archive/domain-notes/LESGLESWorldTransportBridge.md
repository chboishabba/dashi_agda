# LES/GLES World Transport Bridge

This note records the bounded DASHI surface for:

```text
high-fidelity simulation
  -> LES / invariant quotient
  -> fast GLES-style world runner
  -> conformance residual
```

The corresponding Agda module is:

```text
DASHI.Computation.LESGLESWorldTransportBridge
```

## Reading

The bridge treats a game-like or GLES runner as a receipt-gated approximate
transport artifact.  A high-fidelity world state may be reduced to a
large-eddy / latent invariant quotient, replayed by a fast runner, and compared
back through an explicit conformance residual.

The Agda surface carries separate gates for high-fidelity simulation receipts,
quotient receipts, runner determinism, residual definition, side-information
accounting, empirical conformance, and light-transport closure.

## Non-Claims

The module explicitly blocks:

- full physical exactness;
- global `O(1)` world-update claims;
- empirical conformance without receipts;
- discarded residuals;
- uncounted runner side information;
- invertibility of the latent quotient;
- identity between the GLES runner and the high-fidelity simulator.

The safe claim is narrower: a supplied high-fidelity state can be routed through
an explicit quotient and fast runner, but promotion requires the residual and
empirical receipts named by the bridge.

## Validation

Focused check:

```text
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Computation/LESGLESWorldTransportBridge.agda
```
