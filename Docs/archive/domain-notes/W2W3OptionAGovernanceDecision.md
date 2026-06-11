# W2/W3 Option A Governance Decision

Date: `2026-05-13`
Status: `authorized internally; non-promoting until exact token hooks exist`
Scope: `W2/W3 bounded self-issuance only`

## Decision

Option A is accepted as a bounded internal self-issuance policy for the W2 and
W3 lanes.

```text
externalClaim = false
internalClaim = true
scopeBounded = true
```

This decision authorizes the repository to treat the currently bound W2/W3
evidence packets as eligible for internal self-issuance under
`Docs/DASHIGovernanceSelfIssuancePolicy.md`.

It does not create external authority, does not supersede any later external
review, and does not permit broad W2/W3/G5/W4/W5/W8 or unification claims.

## Current Typed Boundary

The exact authority-token datatypes remain constructorless:

```text
NaturalP2ConvergencePromotionAuthorityToken
W3AcceptedEvidenceAuthorityToken
```

Therefore the current typed status is:

```text
Option A authorized = true
tokenProducingHookAuthorizedNow = false
W2 authority token constructed = false
W3 authority token constructed = false
```

## Exact Remaining Blockers

- Add a non-postulated token-producing hook or constructor whose result type is
  exactly `NaturalP2ConvergencePromotionAuthorityToken`.
- Add a non-postulated token-producing hook or constructor whose result type is
  exactly `W3AcceptedEvidenceAuthorityToken`.
- For W2, package the remaining non-authority natural/p2 payload fields before
  the broader W2 promotion receipt can close.

Until those hooks exist, `W2W3OptionASelfIssuanceDecisionReceipt` records an
authorized internal policy decision only. It is not a W2 or W3 promotion
receipt.
