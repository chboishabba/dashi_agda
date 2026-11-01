# W2 External Authority Provider Request

Date: `2026-05-13`
Status: `provider request; blocked; non-promoting`
Owner: `Lane 6`

This packet asks a W2 authority provider or explicitly authorized governance
hook to supply the exact missing W2 authority identity. It does not construct
the token locally.

## Requested Authority Identity

```text
NaturalP2ConvergencePromotionAuthorityToken
```

Accepted alternatives must be exactly equivalent: a non-postulated typed
governance hook or receipt that inhabits the same token boundary and is scoped
only to W2 natural-p2-convergence.

## Evidence And Source Artifacts

| Artifact | Role |
|---|---|
| `DASHI/Physics/Closure/W2W3ExternalAuthorityFormalClosureRequest.agda` | records W2/W3 as pending external authority receipts |
| `DASHI/Physics/Closure/W2W3GovernancePolicyHookRequest.agda` | records that current policy can be consumed but does not authorize token construction |
| `DASHI/Physics/Closure/W2GovernanceTokenConstructorObstruction.agda` | records the missing W2 token constructor obstruction |
| `DASHI/Physics/Closure/NaturalP2ConvergencePromotionObligation.agda` | names the W2 authority token and promotion receipt boundary |
| `Docs/W2GovernanceTokenConstructorObstruction.md` | human-readable obstruction and remaining payload fields |
| `Docs/W2W3AuthorityGovernanceFork.md` | governance fork and no-overreach policy context |

## Exact Receipt Shape Needed

An accepted W2 response must provide:

- provider identity, authority scope, contact or trace id, and timestamp;
- decision: `accepted`, `rejected`, or `insufficient`;
- exact statement that the response supplies or rejects
  `NaturalP2ConvergencePromotionAuthorityToken`;
- evidence packet identity and revision being accepted;
- audit and revocation conditions;
- no-overreach clauses stating no W3, W4, W5, W8, W9, GR/QFT, or paper
  promotion follows;
- if accepted, a typed route usable as the `promotionAuthority` field of the
  W2 promotion receipt.

The downstream W2 receipt still needs the non-candidate W2 payload fields
recorded in the obligation surface, including natural p2 bridge packaging,
naturality/coherence laws, carrier transport preserving convergence, and
carrier-general realization-uniform convergence.

## Non-Promotion Boundary

```text
promotesW2 = false
authorityTokenConstructedHere = false
```

This request is not a proof, token, or receipt. W2 remains blocked until a real
accepted token or exact token-producing governance hook is supplied.
