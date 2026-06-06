# YM Sprint 121 GG1 Compact Group Parameter Table

Route decision: `finite-computation-artifact-only`

Clay promotion: `false`

## Conservative k_G rule

Set `k_G = dim(ad G)` as the conservative real Lie-algebra component count. Fixed compact simple groups receive integer values; symbolic families retain exact formulas over the stated domains.

## Table

| Key | Class | Domain | dim(ad G) | Rank | conservative k_G | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| SU(2) | classical | N = 2 | `3` | `1` | `3` | Compact simply connected A1 representative; locally isomorphic to SO(3). |
| SU(3) | classical | N = 3 | `8` | `2` | `8` | Compact A2 representative used as the non-abelian color baseline. |
| SU(N) | classical family | N >= 2 | `N^2 - 1` | `N - 1` | `N^2 - 1` | Symbolic A_{N-1} family; dimension is retained as an exact formula. |
| SO(N) | classical family | N >= 3, excluding the non-simple SO(4) Lie algebra split | `N(N - 1)/2` | `floor(N/2)` | `N(N - 1)/2` | Compact orthogonal family; SO(4) is recorded as excluded because so(4) = su(2) + su(2). |
| Sp(N) | classical family | N >= 1 | `N(2N + 1)` | `N` | `N(2N + 1)` | Compact symplectic C_N convention, also written USp(2N). |
| G2 | exceptional | fixed | `14` | `2` | `14` | Smallest exceptional compact simple Lie group. |
| F4 | exceptional | fixed | `52` | `4` | `52` | Exceptional compact simple Lie group. |
| E6 | exceptional | fixed | `78` | `6` | `78` | Exceptional compact simple Lie group. |
| E7 | exceptional | fixed | `133` | `7` | `133` | Exceptional compact simple Lie group. |
| E8 | exceptional | fixed | `248` | `8` | `248` | Exceptional compact simple Lie group. |

## Boundary

- Deterministic finite computation only.
- No external data inputs.
- No tests edited.
- No Clay promotion, continuum theorem, or mass-gap claim is emitted.

## Summary

- Entries: `10`
- Concrete entries: `7`
- Max concrete conservative k_G: `248`
