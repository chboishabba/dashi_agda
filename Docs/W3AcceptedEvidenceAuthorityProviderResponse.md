# W3 Accepted Evidence Authority Provider Response

Date: `2026-05-06`
Status: `awaiting provider response; non-promoting`
Owner: `Curie-W3`

This packet is the human-facing response form for the final W3 accepted evidence
authority token handoff. It consumes the request-only packet in:

```text
DASHI/Physics/Closure/W3AcceptedEvidenceAuthorityTokenIntakeRequest.agda
```

It does not create or imply a local
`DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken`.
That token remains constructorless in the repo and must come from an accepted
external authority.

## Required Provider Response

The provider response must include every field below.

| Field | Required content |
|---|---|
| Provider identity | Organization/person/system, authority scope, contact or trace id, and response timestamp |
| Evidence authority decision | One of `accepted`, `rejected`, or `insufficient` |
| HEPData DOI | `10.17182/hepdata.104472` plus submission/table refs `10.17182/hepdata.115656.v1`, `t43`, and `t44` |
| CMS paper DOI | `10.1140/epjc/s10052-023-11631-7` |
| Frozen commit | `3205d746639568762c9e97adf4a3672c356bd491` |
| Comparison law | Bounded below-Z `t43` per-bin comparison under the unnormalized differential cross-section ratio convention |
| Covariance/source | HEPData covariance table `t44`, including source, checksum, or provider equivalent |
| Non-collapse witness | Bin `12`, prediction `0.0486590199823977`, data `0.049758`, uncertainty `0.00048197510309143566`, pull `-2.280159308132989` |
| Status | Exact status: `accepted`, `rejected`, or `insufficient` |
| Exact rejection reason | Required for `rejected` and `insufficient`; must name the failed field or authority rule |

## Accepted Response

An `accepted` response must explicitly state that the external authority accepts
the evidence packet as sufficient to supply:

```text
DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken
```

The response must also bind that token to the provider identity, DOI fields,
frozen commit, comparison law, covariance source, and non-collapse witness above.
The local repo still does not fabricate the token; the accepted response is only
usable after the external token is supplied through the typed receipt surface.

## Rejected Response

A `rejected` response must name the exact rejection reason. Valid rejection
classes include:

```text
provider identity not accepted
HEPData DOI mismatch
CMS paper DOI mismatch
frozen commit mismatch
comparison law rejected or underspecified
covariance/source rejected or underspecified
non-collapse witness rejected or not reproduced
authority scope does not permit W3AcceptedEvidenceAuthorityToken issuance
```

## Insufficient Response

An `insufficient` response must name the missing field or missing authority rule.
It is not a rejection of the W3 packet; it is a typed request for additional
evidence before an accepted/rejected decision can be made.

## Current Local State

The canonical local instance is still:

```text
awaitingProviderResponse
authorityTokenConstructedHere = false
responseContainsAcceptedToken = false
exactRemainingGap = W3AcceptedEvidenceAuthorityToken
```

No downstream W3 consumable anchor, evidence-backed empirical target,
accepted-authority external receipt, B4 empirical promotion, W8 origin promotion,
or broad empirical adequacy claim follows from this response template alone.
