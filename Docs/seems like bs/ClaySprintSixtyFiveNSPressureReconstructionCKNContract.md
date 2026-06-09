# Clay Sprint Sixty Five NS Pressure Reconstruction / CKN Contract

Sprint 65 removes the artifact-level pressure blocker found by Sprint 64.

## Pressure Contract

The CFD producer reconstructs periodic zero-mean pressure from velocity
snapshots:

```text
Delta p = - sum_ij (partial_i u_j) (partial_j u_i)
mean(p) = 0 per saved frame
```

The reconstructed pressure supplies the CKN-compatible term:

```text
r^-2 integral_Q |p|^(3/2) dx dt
```

## dashiCFD Results

Six-run N32/N64 pressure reconstruction:

```text
max_poisson_relative_residual_rms = 3.5409688067143674e-16
```

Pressure-present Sprint 64 rerun:

```text
route_decision = LOCAL_CRITICAL_CONCENTRATION_MIXED
ascended_fraction = 0.9890491452991453
max_local_concentration_ratio = 60.83081878566949
```

N128 seed0 and dense N64 seed0 also route as mixed.

## Governance

Sprint 65 proves no CKN theorem.  It only makes the pressure-inclusive local
concentration diagnostic available.  Threshold calibration, suitable weak
solution bridge, continuum uniformity, no finite-time blowup, and Clay/NS
promotion remain open.
