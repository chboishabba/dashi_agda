# Observer-Conditioned Transport Bridge

## Status

Candidate-only bridge. This document does not promote a quotient construction, an exact caustic solver, physical equivalence to a full wave or light-transport solver, or a computational speedup theorem.

The checked surface is:

- `DASHI.Physics.ObserverConditionedTransportBridge`
- `DASHI.Physics.ObserverConditionedTransportRegression`

## Shared transport shape

Acoustic simulation and light transport can both be represented by:

1. a source or excitation,
2. a transport state,
3. a transport update,
4. an observer projection,
5. an observed sample.

For engine sound, the observer can be a microphone and the sample can be a pressure or waveform sample. For rendering, the observer can be a pixel and the sample can be radiance.

The Agda bridge packages this as `TransportSystem` with `advance` and `observe` maps.

## Observer-induced equivalence

For a selected observer `o`, two full states are observer-equivalent when they produce the same sample:

```text
x ≈[o] y  iff  observe o x = observe o y
```

This is deliberately only an equivalence at one observation channel. It does not imply that the states are equal as fields, equal for other observers, or interchangeable for future dynamics.

## Observer-relevant carrier

`ObserverRelevantCarrier` records:

- a candidate reduced state type,
- an encoder from the full transport state,
- a decoder to the observer sample,
- representative soundness for the encoded state.

This is not yet a quotient type or a proof of minimal sufficient statistics. It is the smallest conservative typed surface that expresses the proposed computational order:

```text
full state -> observer-relevant carrier -> observer sample
```

rather than requiring every consumer to evolve or sample the full transport domain.

## Temporal persistence

`TemporalObserverTransport` evolves the relevant carrier across frames. This captures the distinction discussed in relation to RTX motion vectors:

- screen-space motion vectors reproject prior image-space estimates;
- the candidate DASHI bridge evolves a state in transport-relevant space.

No claim is made that this always survives occlusion changes, path births or deaths, specular bifurcations, diffuse transport, nonlinear acoustics, shocks, turbulence, or long-horizon error accumulation.

## Caustic reading

A single caustic point is one possible realization only in a restricted regime. The observer-relevant carrier may instead require:

- one stationary path,
- several stationary paths,
- a fold pair,
- a mode family,
- a short manifold tube,
- diffuse or volumetric residuals.

Accordingly, `singleCausticAlwaysSufficient` is explicitly false in the governance record.

## RTX and wave-solver comparison

The bridge captures a plausible place to win computationally:

- few observers,
- persistent geometry and transport structure,
- a reduced carrier much smaller than the full state,
- cheap cross-frame updates,
- bounded observer error.

But actual speed depends on discovery cost, carrier size, update cost, decode cost, observer count, scene changes, required fidelity, and hardware implementation. Therefore both `fasterThanRTXProved` and `fasterThanWaveSolverProved` remain false.

A defensible benchmark must compare matched outputs and report at least:

- observer error over time,
- phase and transient error,
- state memory,
- initialization/discovery cost,
- per-frame update cost,
- decode cost,
- scaling with observer count,
- failure under path topology changes.

## Relationship to existing DASHI formalism

This tranche follows the repository's established proved/bridge/empirical separation and reuses `DASHI.Core.CandidateOnlyCore`. It should later connect to existing sparse, twist, spectral, wave, MDL, receipt, and runtime surfaces only through explicit adapters, without silently upgrading this candidate bridge into theorem authority.
