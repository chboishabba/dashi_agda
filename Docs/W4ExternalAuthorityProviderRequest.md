# W4 External Authority Provider Request

Date: `2026-05-13`
Status: `provider request; blocked; non-promoting`
Owner: `Lane 6`
Typed surface:
`DASHI.Physics.Closure.W4ExternalAuthorityTokenSurface`

This packet asks for the external authority inputs needed before any W4
Z-window adequacy or physical calibration claim can be considered. It does not
promote W4.

## Requested Authority Identity

Primary authority request:

```text
AcceptedDYLuminosityConventionAuthority
```

W4-specific consumed shape after that authority exists:

```text
W4ZAdequacyReceipt inputs: accepted per-bin luminosity vector ell_i,
normalization/conversion law, covariance/systematic propagation, and
CMS-SMP-20-003 t21/t22 source binding
```

The new request-only token surface is:

```text
DASHI.Physics.Closure.W4ExternalAuthorityTokenSurface.W4ExternalAuthorityToken
```

It is constructorless in-repo. The canonical request pack is:

```text
DASHI.Physics.Closure.W4ExternalAuthorityTokenSurface.canonicalW4ExternalAuthorityProviderRequest
```

## Evidence And Source Artifacts

| Artifact | Role |
|---|---|
| `DASHI/Physics/Closure/W4ExternalAuthorityTokenSurface.agda` | typed constructorless W4 request surface |
| `Docs/AcceptedDYLuminosityConventionAuthorityProviderPacket.md` | provider-facing DY convention request |
| `Docs/W4W5DYConventionCurrentBlocker.md` | current shared W4/W5 DY convention blocker |
| `Docs/DYAuthorityProviderResponseStatus.md` | local provider-response status |
| `Docs/W4ZAdequacyDecisionStatus.md` | W4 adequacy status context |
| `Docs/W4ZAdequacyReceiptTemplate.md` | expected W4 receipt fields |
| `scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv` | public Z-window measurement table |
| `scripts/data/hepdata/ins2079374_Covariance_phistar_mass_76-106_t22.csv` | public Z-window covariance table |
| `logs/research/w4_z_peak_anchor_dirty_run_20260513.json` | negative dirty Z-shape diagnostic |

Current local W4 diagnostic:

| Field | Value |
|---|---:|
| Measurement bins | `18` |
| Covariance shape | `18 x 18` |
| Dirty shape chi2/dof | `298.8462841768543` |

The dirty shape diagnostic is negative. It is not an adequacy receipt.

## Exact Receipt Shape Needed

An accepted W4 response must provide:

- provider identity, authority scope, contact or trace id, and timestamp;
- decision: `accepted`, `replacement`, `rejected`, or `insufficient`;
- PDF set/version, LHAPDF id or equivalent table identity, and grid checksums;
- factorization/renormalization scale rule;
- rapidity/eta/fiducial convention;
- mass-window and phi-star-bin convention for CMS-SMP-20-003;
- W4 per-bin luminosity vector `ell_i` or accepted reproducible computation
  route;
- normalization preservation law and provider-to-runner conversion law;
- covariance/systematic propagation;
- DOI/public URL/source citation and immutable provenance.

If the provider rejects or marks insufficient any field, the response must name
the exact failed rule.

## Exact Typed Fields Requested

The typed surface records the current first-class missing fields:

```text
missingAcceptedDYLuminosityConventionAuthority
missingAcceptedPerBinLuminosityVector
missingInternalDiagonalConvention
missingLeptonChannelCombineConvention
missingZAndBelowZAnchorBinding
missingProviderIdentityAndDate
missingStrictInequalityOrAdequacyThresholdPrimitive
```

The provider must state the luminosity convention for the W4 per-phi-star-bin
`ell_i` vector, the internal diagonal convention consumed by the W4 adequacy
formula, the electron/muon channel-combine convention, and the source binding
for both the Z-window anchor and the below-Z anchor.

Provider/date fields are mandatory: provider identity, role/scope, contact or
trace id, response date, and source citation or artifact retrieval date.

## Non-Promotion Boundary

```text
promotesW4 = false
authorityTokenConstructedHere = false
adequacyReceiptConstructedHere = false
physicalCalibrationReceiptConstructedHere = false
```

No W4 adequacy, physical calibration, matter/stress-energy interface, GR, or
paper claim follows from this request.

Exact remaining blocker:

```text
missingAcceptedDYLuminosityConventionAuthority
```

Even after that authority lands, W4 still requires the accepted per-bin
luminosity vector, diagonal/channel/anchor conventions, provider/date metadata,
and an authority-backed strict inequality or adequacy-threshold primitive before
any W4 adequacy receipt can be considered.
