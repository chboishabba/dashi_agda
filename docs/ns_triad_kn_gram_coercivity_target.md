# NS triad `K_N(A)` Gram coercivity target

Date: 2026-06-25

## Status Lock

Retired:
- positive-sector Schur norm as the theorem carrier
- ACL cancellation as the controlling route
- bare `L_FT^+` proxy as the live object

Live:
- high-high amplitude-weighted Gram coercivity for the exact signed triad carrier

Measured:
- the exact scripted pair-incidence object is canonicalized
- the sampled shell rows still show a positive Gram-side floor with small cross-block interference
- candidate evidence motivates the `c / N` Gram-coercivity target, but that scale is not promoted here as a theorem

Open theorem:
- `inf_A lambda_min(K_N(A)) >= c / N`

This note is fail-closed. It records the live theorem target and the next proof
split only. It does not promote theorem authority, full-NS promotion, BKM
exclusion, or Clay promotion.

## Canonical Object

Use the amplitude-weighted signed high-high triad Gram matrix

`K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)`

as the theorem object. The admissible profile `A` belongs to the high-high
amplitude class under which the exact scripted pair-incidence operator is
defined.

The target is the Rayleigh lower bound

`lambda_min(K_N(A)) = inf_{|v|_2 = 1} <v, K_N(A) v>`

and the live theorem goal is

`<v, K_N(A) v> >= (c / N) * |v|_2^2`

for every admissible profile `A` and every test vector `v`.

## Proof Split

1. `K_N(A)` exactness
   - Show that the sampled scripted matrix is exactly the algebraic
     amplitude-weighted Gram object.
2. Diagonal mass lower bound
   - Isolate the self-frame contribution and prove a lower bound of order `c_diag / N`.
3. Coherence / off-diagonal control
   - Bound cross-triad interference by `c_off / N` with `c_off < c_diag`.
4. Admissible profile condition
   - State the exact high-high amplitude class on which the bound is valid.

Then the intended min-max closure is

`lambda_min(K_N(A)) >= (c_diag - c_off) / N`.

## Current Boundaries

- The exact-object gate is open only at theorem level, not at object-definition level.
- `q_gap / SchurResidueScale` transfer remains open.
- Structural BKM projection smallness remains open.
- Residence-time exclusion remains open.
- Clay promotion remains false.

## Diagnostic Artifact

The supporting diagnostic for this target is

- `scripts/ns_triad_kn_gram_coercivity_decomposition.py`

It reads the canonical sampled shell rows and decomposes the sampled
`lambda_min` floor into diagonal-vs-cross Gram contributions, coherence proxy,
profile spread, and worst-eigenvector support. That diagnostic is candidate-only
and exists to sharpen the proof split above, not to replace it.
