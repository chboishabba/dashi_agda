# External Authority Packet V2

Date: `2026-05-13`
Status: `per-gate provider packet index; awaiting external authority; non-promoting`
Owner: `Lane 6`

This V2 packet splits the W2/W3/W4/W5 external authority requests into
sendable per-gate artifacts. It does not close any external gate and does not
construct authority tokens locally.

## Non-Promotion Boundary

```text
externalTokensPresent = false
authorityTokenConstructedHere = false
promotesW2 = false
promotesW3 = false
promotesW4 = false
promotesW5 = false
paperPromotion = false
```

Accepted provider responses may cover only the exact gate and receipt named in
the matching per-gate packet. No cross-gate promotion follows by implication.

## Sendable Packets

| Gate | Provider packet | Requested authority identity | Current local status |
|---|---|---|---|
| W2 | `Docs/W2ExternalAuthorityProviderRequest.md` | `NaturalP2ConvergencePromotionAuthorityToken` or equivalent exact token-producing governance hook | blocked; no token constructor or accepted authority receipt |
| W3 | `Docs/W3ExternalAuthorityProviderRequest.md` | `W3AcceptedEvidenceAuthorityToken` | candidate pass, no accepted token |
| W4 | `Docs/W4ExternalAuthorityProviderRequest.md` | accepted Drell-Yan luminosity convention and W4 Z-window adequacy receipt inputs | blocked; dirty Z-shape diagnostic is negative and no accepted DY convention exists |
| W5 | `Docs/W5ExternalAuthorityProviderRequest.md` | accepted `A(M, phi*)` bridge or accepted observable-conversion/retarget law, plus DY/PDF convention if W5 remains on the old correction surface | blocked; public phi-star ratios are diagnostic only |

## Shared Evidence Index

Typed aggregate surface:

```text
DASHI.Physics.Closure.W2W3W4W5ExternalAuthorityPacketSurface
```

Human aggregate summary:

```text
Docs/ExternalAuthorityPacket.md
```

The aggregate packet remains useful as a one-page index. The per-gate packets
are the artifacts to send to external providers.

## W4/W5 Ratio Boundary

The public CMS-SMP-20-003 / HEPData `ins2079374` phi-star ratio diagnostic is:

| Diagnostic | Value |
|---|---:|
| `t43/Z` | `0.048798342138242475` |
| `t45/Z` | `0.025440376842598356` |
| `t45/t43` | `0.5213369087525034` |

These values are from public `DSIG/DPHISTAR` ratio-table integrals. They are
not the older W5 PDF-carrier target `0.8804486068`, not a `d sigma / dM`
mass-window ratio, and not an accepted W4/W5 conversion law.

## Expected Provider Response Classes

Each per-gate packet accepts the same top-level response classes:

```text
accepted
rejected
insufficient
```

An `accepted` response must name the exact authority identity, bind the cited
source artifacts and checksums or immutable provider equivalents, identify the
provider authority scope, and state the no-overclaim boundary for all gates not
covered by that response.
