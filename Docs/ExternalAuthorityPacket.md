# External Authority Packet

Date: `2026-05-13`
Status: `evidence-index export; awaiting external authority; non-promoting`
Owner: `Worker External Packet`

This packet is a concise human-facing export of the W2, W3, W4, and W5
authority state. It summarizes available evidence and the exact missing
authority artifacts without creating, implying, or self-issuing external
tokens.

Per-gate sendable packet set:

```text
Docs/ExternalAuthorityPacketV2.md
Docs/W2ExternalAuthorityProviderRequest.md
Docs/W3ExternalAuthorityProviderRequest.md
Docs/W4ExternalAuthorityProviderRequest.md
Docs/W5ExternalAuthorityProviderRequest.md
```

Use the per-gate packet when a provider needs a directly actionable request for
one gate. This aggregate remains an index and non-overclaiming summary.

Typed aggregate surface:

```text
DASHI.Physics.Closure.W2W3W4W5ExternalAuthorityPacketSurface
```

## Non-Overclaiming Boundary

Current local status:

```text
externalTokensPresent = false
authorityTokenConstructedHere = false
promotesW2 = false
promotesW3 = false
promotesW4 = false
promotesW5 = false
paperPromotion = false
```

No local document or module in this packet claims that external authority
tokens exist. The packet is an export/request index only.

## W2 Evidence And Gap

Available local evidence surfaces:

```text
DASHI.Physics.Closure.W2W3ExternalAuthorityFormalClosureRequest
DASHI.Physics.Closure.W2W3GovernancePolicyHookRequest
DASHI.Physics.Closure.W2GovernanceTokenConstructorObstruction
DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation
```

The current W2 evidence records policy consumption and local mathematical /
dynamical support surfaces, including normalizeAdd-style stability,
sum/p-adic invariance pressure, natural-p2 bridge packaging, carrier transport,
and carrier-general convergence obligations.

Missing authority artifact:

```text
NaturalP2ConvergencePromotionAuthorityToken
```

Current status: W2 remains pending an external authority value or accepted
receipt for the exact token. The repo does not construct the token locally.

## W3 Evidence And Gap

Available local evidence surfaces:

```text
DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptRequestPack
DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate
DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenGovernanceObstruction
Docs/W3AcceptedEvidenceAuthorityProviderResponse.md
```

Current W3 diagnostics:

| Field | Value |
|---|---|
| Frozen commit | `3205d746639568762c9e97adf4a3672c356bd491` |
| Comparison artifact | `logs/research/w3_frozen_3205d74_t43_comparison_20260513.json` |
| Artifact SHA-256 | `92b61032c06cb4d00d22e00bf9e280b47806f9ebf18f012f5b82a41b0afae238` |
| Status | `candidate-pass-no-authority-token` |
| chi2/dof | `2.1565` |
| mean pred/data | `0.9941` |

Missing authority artifact:

```text
W3AcceptedEvidenceAuthorityToken
```

Current status: the canonical t43/t44 evidence and frozen comparison are
available as candidate evidence, but W3 remains pending an accepted external
authority response or an explicitly authorized governance receipt. No W3
accepted evidence authority token exists in this packet.

## W4/W5 Evidence And Gap

Available local evidence surfaces:

```text
DASHI.Physics.Closure.W4W5PublicHEPDataRatioDiagnostic
DASHI.Physics.Closure.W4W5PhiStarToMassAcceptanceBridgeRequest
DASHI.Physics.Closure.W5CT18ExternalIntakeReceipt
Docs/W4W5DYConventionCurrentBlocker.md
Docs/W4W5AcceptanceBridgeProviderRequest.md
Docs/DYAuthorityProviderResponseStatus.md
```

Supported public HEPData `DSIG/DPHISTAR` ratio diagnostics, computed from
the public CMS-SMP-20-003 / HEPData `ins2079374` CSV cache:

| Diagnostic | Value |
|---|---:|
| `t43/Z` | `0.048798342138242475` |
| `t45/Z` | `0.025440376842598356` |
| `t45/t43` | `0.5213369087525034` |

Provenance:

| Field | Bound value |
|---|---|
| Runner | `scripts/run_w4w5_hepdata_public_ratio_integral.py` |
| Output artifact | `scripts/data/outputs/w4w5_hepdata_public_ratio_integral.json` |
| Z denominator table | `10.17182/hepdata.115656.v1/t21` |
| Below-Z ratio table | `10.17182/hepdata.115656.v1/t43` |
| Above-Z ratio table | `10.17182/hepdata.115656.v1/t45` |
| Formula | `sum Ratio_i * (dsigma_Z/dphistar)_i * dphistar_i / sum (dsigma_Z/dphistar)_i * dphistar_i` |
| Public record | `https://www.hepdata.net/record/ins2079374` |
| CMS public page | `https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/` |
| CMS submission YAML | `https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/submission.yaml` |

Interpretation boundary:

- `t21` is an absolute `DSIG/DPHISTAR` Z-window denominator table for
  `76 <= M_ll < 106 GeV`.
- `t43` is a public ratio table for `50 <= M_ll < 76 GeV` over
  `76 <= M_ll < 106 GeV`.
- `t45` is a public ratio table for `106 <= M_ll < 170 GeV` over
  `76 <= M_ll < 106 GeV`.
- The public-ratio result `t45/t43 = 0.5213369087525034` is not the older
  W5 PDF-carrier target `0.8804486068`.
- These numbers are public ratio-table diagnostics only. They do not establish
  a mass-integrated cross-section ratio, a PDF correction target, or an
  accepted DY luminosity convention.

Missing authority artifact:

```text
accepted A(M,phi*) bridge or accepted observable-conversion law
```

Exact missing field:

```text
central-value acceptance/efficiency surface A(M, phi*) for the
CMS-SMP-20-003 mass windows 50-76, 76-106, and 106-170 GeV, or an accepted
observable-conversion law from DSIG/DPHISTAR ratio-table integrals to
mass-integrated cross-section/PDF correction ratios
```

Current status: W4/W5 remain blocked on an accepted phi-star-to-mass
acceptance/efficiency bridge, or an accepted observable-conversion law that
states how these public `DSIG/DPHISTAR` ratio-table integrals may be compared
to the W4/W5 mass-integrated cross-section/PDF correction surface. The public
tables, covariance matrices, uncertainty columns, and response matrices do not
themselves supply `A(M,phi*)`. This packet does not promote W4 or W5.

## Current Export Verdict

The current packet is suitable to send as an external authority request/index.
It documents evidence availability for W2/W3/W4/W5 and identifies the missing
accepted authority artifacts. It is not a closure certificate.

Next admissible external response classes:

```text
accepted
rejected
insufficient
```

Any accepted response must name the exact authority token or accepted bridge,
bind the cited evidence/provenance, and preserve the non-overclaiming boundary
for lanes not covered by that response.
