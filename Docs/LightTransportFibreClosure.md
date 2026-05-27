# Light Transport Fibre Closure

This note records the DASHI-side formal surface for the current light transport
claim:

```text
scene / unlit viewport
  -> photon or viewport-pixel carrier
  -> geometry/material/spectral/visibility fibres
  -> closed transport operator
  -> lit viewport
```

The corresponding Agda module is:

```text
DASHI.Physics.Closure.LightTransportFibreClosure
```

## Reading

The important shift from the current `dashiRTX` prototype is that the transport
operator itself becomes the retained latent artifact.  The existing prototype
mostly learns or optimizes where to refresh; this surface names the stronger
target:

```text
weighted fibre mixing
  + closure receipts
  + explicit residual defects
  + counted side information
```

Diffuse surfaces are modelled as broad fibre splitting, specular surfaces as
near-permutation transport, colour as a spectral transform, and subsurface
scattering as an internal closure chart.

## Non-Claims

The module explicitly blocks:

- global physically exact `O(1)` rendering claims;
- closed transport reuse without a closure receipt;
- treating a denoiser as a physics proof;
- discarding residual defects;
- ignoring side information;
- promoting material laws without receipts.

The safe claim is narrower: if a local transport closure is receipted and its
defect is admissible, the renderer may apply that closure as a deterministic
local transport artifact.

## LES/GLES Bridge

`DASHI.Computation.LESGLESWorldTransportBridge` consumes this closure
vocabulary as one gate in a separate computation lane:

```text
high-fidelity simulation
  -> LES / invariant quotient
  -> fast GLES-style world runner
  -> conformance residual
```

That lane is intentionally theorem-thin. It does not promote physical
exactness, global `O(1)` update, or empirical conformance without the named
simulation, quotient, runner, residual, side-information, and empirical
receipts.

## Validation

Focused check:

```text
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Physics/Closure/LightTransportFibreClosure.agda
```
