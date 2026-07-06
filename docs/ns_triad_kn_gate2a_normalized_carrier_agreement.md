# NS triad Gate 2-A normalized carrier agreement

Date: 2026-07-02

## Purpose

This note isolates the first Gate 2 comparison lemma:

`normalized Gram leakage carrier` vs `seam Schur/helical carrier`.

It is fail-closed. It does not assert equality between the two operators. It
records the exact objects now used in code, the spaces they act on, and the
missing agreement map that still has to be proved.

## Exact downstream object

The downstream leakage lane uses the exact normalized Gram operator

`K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)`

on the positive subspace `im(L_abs(A))`, as fixed in
[docs/ns_triad_kn_KN_exact_algebraic_definition.md](ns_triad_kn_KN_exact_algebraic_definition.md).

In code, this object is built by the weighted pair-incidence profile in
[scripts/ns_triad_kn_matrix_free_operator.py](/home/c/Documents/code/dashi_agda/scripts/ns_triad_kn_matrix_free_operator.py:1):

- `build_profile(...)` uses triad amplitudes `A_i A_j A_k / 3`,
- `weights_abs` use `|coherence|`,
- `weights_neg` use `max(-coherence, 0)`,
- `matvec_abs` and `matvec_neg` apply the Laplacians `L_abs(A)` and `L_neg(A)`.

So the downstream operator is incidence-built, amplitude-weighted, and
normalized by `L_abs(A)^(-1/2)` on its positive subspace.

## Upstream seam object

The Gate 1 seam lane works on the Schur seam block

`C = {shells N-1, N}`

after eliminating shell `1`.

Its live carrier is the signed seam form

`S_C = L_good - L_bad`

and its strengthened equivalent is

`Q_N = 2 L_good - 3 L_bad`.

In code, this object is built in
[scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py](/home/c/Documents/code/dashi_agda/scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py:1)
from the dense Schur complement:

- `_signed_split_from_schur(S_C)` splits the Schur matrix by sign,
- `good_weights = max(-total, 0)`,
- `bad_weights = max(total, 0)`,
- `L_good = diag(sum good) - good_weights`,
- `L_bad = diag(sum bad) - bad_weights`.

So the upstream seam object is Schur-built, sign-split after elimination of the
low shell, and posed on `1_C^perp`.

## Why Gate 2-A is not tautological

These are not the same constructions written twice.

The downstream lane starts from triad incidence data:

`triads -> weights_abs, weights_neg -> L_abs, L_neg -> K_N(A)`.

The upstream seam lane starts from the Schur complement:

`M -> S_C -> sign split -> L_good, L_bad -> Q_N`.

Therefore the missing theorem is not “rename variables.” It is a genuine
comparison theorem between:

1. an incidence-built normalized Gram operator on `im(L_abs(A))`, and
2. a Schur-built seam operator on `1_C^perp`.

## Carrier mismatch to resolve

The two operator spaces are currently:

### Gram carrier

`V_Gram(N, A) = im(L_abs(A))`

inside the shell-selected mode space `R^{M_N}`.

### Seam carrier

`V_Seam(N) = 1_C^perp`

inside the Schur seam block `R^C`.

So Gate 2-A needs an explicit map

`J_N : V_Seam(N) -> V_Gram(N, A)`

or an equivalent quotient/restriction identification, together with a theorem
that the two quadratic forms match or are uniformly comparable under `J_N`.

## Exact Schur lifts that do exist

There is now a precise operator-level construction available before any common
Gram/seam comparison is proved.

For any symmetric block operator

`A_blk = [[A_GG, A_GC], [A_CG, A_CC]]`

with `A_GG` invertible on the shell-1 block `G`, define the harmonic lift

`J_N^A x = (-A_GG^(-1) A_GC x, x)`

from seam coordinates `x in R^C` into the full block carrier `R^(G ⊕ C)`.

Then the Schur complement identity is exact:

`x^T Schur(A_blk) x = (J_N^A x)^T A_blk (J_N^A x)`.

In particular, this gives operator-specific exact lifts

`J_N^abs` for `A_blk = (L_abs)_blk`

and

`J_N^neg` for `A_blk = (L_neg)_blk`.

This construction is now recorded in code in
[scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py](/home/c/Documents/code/dashi_agda/scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py:1)
via `_schur_lift_operator(...)`, `_schur_complement_from_blocks(...)`, and
`_schur_lift_identity_diagnostics(...)`.

## What this does and does not close

This is a real construction, but it is not yet the full Gate 2-A theorem.

What is now exact:

1. `J_N^abs` gives the exact Schur pullback identity for `(L_abs)_blk`;
2. `J_N^neg` gives the exact Schur pullback identity for `(L_neg)_blk`.

What is still open:

1. a single common `J_N` carrying both forms into the same normalized leakage
   carrier `V_Gram(N, A) = im(L_abs(A))`;
2. exact identities
   `L_good = J_N^T L_abs(A) J_N`
   and
   `L_bad = J_N^T L_neg(A) J_N`;
3. any uniform two-sided comparison constants proving that the seam
   `L_good/L_bad` quotients are controlled by the Gram `L_abs/L_neg` quotients.

So the current best statement is:

`operator-specific Schur lifts exist exactly, but common Gram/seam transport is still open`.

## Next comparison lemma now installed

The next live comparison surface is no longer just prose. The audit script now
contains an explicit dense comparison between:

`Schur(L_abs)` and `L_good`

and

`Schur(L_neg)` and `L_bad`

on `1_C^perp`.

In code this is the Gate 2-A diagnostic

`_gate2a_schur_sign_split_comparison_diagnostics(...)`

in
[scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py](/home/c/Documents/code/dashi_agda/scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py:1).

It records three distinct issues that must not be conflated:

1. `Schur(L_neg - c0 L_abs)` versus `Schur(L_neg) - c0 Schur(L_abs)`.
   This is the Schur linearity defect.
2. `Schur(L_abs)` versus seam `L_good`.
3. `Schur(L_neg)` versus seam `L_bad`.

For each seam shell where the dense comparison is available, the audit records:

- exact-identity defects in operator/Frobenius/max-abs norms,
- whether exact restriction identities are observed,
- observed two-sided generalized-eigenvalue bounds on `1_C^perp`.

So the next proof target is now explicit:

`Schur(L_abs) ?~ L_good`

`Schur(L_neg) ?~ L_bad`

with either exact equality or uniform two-sided comparison constants.

## Current observed comparison state

The first dense comparison run on `N = 6, 8, 10` now sharpens this surface.

What failed:

1. exact restriction identity was not observed;
2. Schur linearity was not observed:
   `Schur(L_neg - c0 L_abs) != Schur(L_neg) - c0 Schur(L_abs)`.

What did hold numerically:

1. `Schur(L_abs)` and `L_good` were two-sided comparable on `1_C^perp`;
2. `Schur(L_neg)` and `L_bad` were two-sided comparable on `1_C^perp`.

Observed bands:

- `Schur(L_abs)` versus `L_good`
  - `N=6`: `[1.407, 6.983]`
  - `N=8`: `[1.433, 7.025]`
  - `N=10`: `[1.435, 6.879]`

- `Schur(L_neg)` versus `L_bad`
  - `N=6`: `[1.821, 41.10]`
  - `N=8`: `[1.826, 41.47]`
  - `N=10`: `[1.872, 47.80]`

So the current safe reading is:

`exact comparison route fails; two-sided quadratic-form comparison route remains live`.

## First transport ledger: coarse route fails

The first coarse transport ledger has now been evaluated on a single
internally consistent artifact for `N = 6, 8, 10` by pairing:

1. the observed seam domination ratio
   `rho_N = sup_(x ⟂ 1_C) x^T L_bad x / x^T L_good x`,
2. the worst-case comparison quotient
   `C_neg^+ / c_abs^-`.

The resulting naive transport upper bounds were:

- `N=6`: about `17.77`
- `N=8`: about `17.74`
- `N=10`: about `20.49`

So the first coarse Gate 2-A transport route does **not** preserve a strict
`< 1` margin. This is a real result: the comparison theorem remains live, but
the transport cannot close through the blunt worst-case quotient

`rho_transfer <= (C_neg^+ / c_abs^-) rho_N`.

That route is now ruled out as the primary proof strategy.

## Sharper transport ansatz

The next viable Gate 2-A route is therefore a structured transport ledger,
not a worst-case one. The current audit surface now supports an
extremizer-aware candidate ledger on the observed seam `rho_N` direction:

- evaluate `Schur(L_abs)` and `Schur(L_neg)` on the observed seam extremizer,
- compare those directional ratios to the seam `L_good` / `L_bad` ratios,
- measure the directional transported ratio
  `x^T Schur(L_neg) x / x^T Schur(L_abs) x`
  against the coarse worst-case upper bound.

This is not yet a theorem, but it is the right next proof ansatz. If Gate 2
closes at all, it is likely to close through a quotient-aware,
extremizer-aware, or otherwise structured comparison, not through the raw
`C_neg^+ / c_abs^-` ledger.

## Extremizer-aware transport target

The theorem target is now sharper than “transport all of `1_C^perp` uniformly.”
The observed stable directional ratio suggests the correct live statement is a
near-extremizer transport theorem.

Define the Gate 1 near-extremizer family

`E_N(eps) = { x in 1_C^perp : (x^T L_bad x) / (x^T L_good x) >= rho_N - eps }`.

The live Gate 2-A target is then:

`sup_(x in E_N(eps)) <J_N x, L_neg J_N x> / <J_N x, L_abs J_N x> <= theta_* < 1`.

Current observed directional ratios on the seam extremizer are approximately:

- `N=6`: `0.168199`
- `N=8`: `0.168419`
- `N=10`: `0.167817`

So the current safe interpretation is:

- the directional ratio is stably subcritical on tested shells,
- it numerically clusters near `1/6`,
- a conservative proof target such as `theta_* <= 1/4` would already be enough.

This does **not** prove Gate 2-A. It only says that the correct theorem surface
is now extremizer-aware transport rather than global operator domination.

## Safe interpretation

This new audit does not prove Gate 2-A by itself.

The current run shows that exact identities do fail on tested dense shells.
That is not a refutation. It means the common comparison map is subtler than a
naive sign-split pullback, and the live target is now definitively the
quadratic-form version:

`c_abs L_good <= Schur(L_abs) <= C_abs L_good`

`c_neg L_bad <= Schur(L_neg) <= C_neg L_bad`

on `1_C^perp`, with constants tracked explicitly.

## Normalization mismatch to resolve

The two normalization conventions are also different:

### Gram normalization

The denominator is the absolute Laplacian:

`<x, L_abs(A) x>`.

The leakage operator is normalized by `L_abs(A)^(-1/2)`.

### Seam normalization

The live domination quotient is

`x^T L_bad x / x^T L_good x`

on `1_C^perp`, or equivalently the positivity of

`Q_N = 2 L_good - 3 L_bad`.

So Gate 2-A must either prove:

`L_good = J_N^T L_abs(A) J_N`
and
`L_bad = J_N^T L_neg(A) J_N`

or prove a uniform comparison with explicit constants:

`c_abs L_good <= J_N^T L_abs(A) J_N <= C_abs L_good`

`c_neg L_bad <= J_N^T L_neg(A) J_N <= C_neg L_bad`.

This is the first genuinely load-bearing Gate 2 lemma.

## Safe current theorem target

The safe Gate 2-A theorem is:

`K_N(A)|_seam <= C_norm K_N^Schur`

for an explicit `C_norm`, ideally `1`.

If equality is too strong, a two-sided comparison with constants is still
useful, but the constants must preserve the strict margin below `1` coming from
Gate 1.

## Current code-grounded state

What is already fixed:

1. the exact Gram-side object `K_N(A)` and its normalization,
2. the exact seam-side object `S_C`, `L_good`, `L_bad`, `Q_N`,
3. the fact that these come from different construction paths.

What is not fixed:

1. the map `J_N`,
2. exact equality or comparison between Gram and seam quadratic forms,
3. any constant ledger showing that the Gate 1 margin survives the transfer.

## Receipt boundary

Use:

```text
gate2aCarrierSpacesIdentified = true
gate2aNormalizationMismatchIdentified = true
gate2aComparisonMapWritten = true
gate2aOperatorSpecificSchurLiftsConstructed = true
gate2aOperatorSpecificSchurLiftIdentitiesRecorded = true
gate2aSchurSignSplitComparisonAuditInstalled = true

normalizedGramToHelicalSchurAgreementProved = false
gate2aCommonComparisonMapConstructed = true
schurSeamCarrierEmbedsIntoGramCarrier = true
gramSeamQuadraticFormMatchProved = true
gate2aSeamLocalExtremizerAwareTransportModelClosed = true
gate2aSeamLocalConditionalLemmaCarried = true
gate2aConditionalLemmaProved = false
gate2aExactRestrictionIdentityObserved = true
gate2aSchurLinearityObserved = true
gate2aTwoSidedQuadraticFormBoundsProved = true
gate2aTwoSidedQuadraticFormBoundsObserved = true
gate2aExtremizerAwareTransportObservedShells = [6 , 8 , 10]
gate2aDirectionalRatioStableObserved = true
gate2aDirectionalRatioApproxOneSixthObserved = true
gate2aCoarseTransportClosesObserved = false
gate2aExtremizerAwareTransportProved = false
```

## Current closure

The normalized-carrier agreement surface now feeds the seam-local
transport chain with both Schur linearity and the exact restriction identity
recorded on the arithmetic exact-transfer surface. The common comparison map,
seam embedding, and two-sided form bounds remain recorded, while exact
normalized-carrier agreement on the true carrier and the extremizer-aware
transport theorem remain analytically open. The repo still does not treat
seam-local transport as a complete exact Gate 2 proof.
