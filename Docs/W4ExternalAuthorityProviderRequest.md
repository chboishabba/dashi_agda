# W4 External Authority Provider Request

Date: `2026-05-13`
Status: `provider request; blocked; non-promoting`
Owner: `Lane 6`
Typed surface:
`DASHI.Physics.Closure.W4ExternalAuthorityTokenSurface`

This packet asks for the external authority inputs needed before any W4
Z-window adequacy or physical calibration claim can be considered. It does not
promote W4.

## Public-Source Self-Population Attempt

The typed surface now records a fail-closed public-source self-population
attempt:

```text
DASHI.Physics.Closure.W4ExternalAuthorityTokenSurface.canonicalW4PublicSourceAuthoritySelfPopulationAttempt
```

The authority basis is public paper/data:

```text
authorityBasis = publicCMSPaperAndHEPData
externalClaim = false
```

This does not claim a CMS response or external countersignature. It records
CMS-SMP-20-003 / HEPData `ins2079374` plus local checksum-bound diagnostics as
the public evidence basis, then fails closed because the exact token and
accepted DY authority result types remain uninhabited.

The governance policy checked for this route is
`Docs/DASHIGovernanceSelfIssuancePolicy.md`. Its current self-issuance ruling
is W2/W3-scoped and explicitly does not cover W4/W5 Drell-Yan convention or
physical-unit authority. Therefore the public-source route is request evidence
only, not a legitimate closure of
`missingAcceptedDYLuminosityConventionAuthority`.

## Policy-Hook Request Surface

No true canonical token-producing hook is present in the current W4 authority
owner surface. The typed request therefore remains fail-closed and records the
exact hook shape needed:

```text
DASHI.Physics.Closure.W4ZAdequacyReceipt.canonicalAcceptedDYLuminosityConventionAuthorityPolicyHookRequest
DASHI.Physics.Closure.W4ExternalAuthorityTokenSurface.canonicalW4LuminosityZAdequacyPolicyHookRequest
```

The canonical definition site is:

```text
DASHI.Physics.Closure.W4ZAdequacyReceipt.AcceptedDYLuminosityConventionAuthority
```

That type remains constructorless. The owner-module hook request records
`firstMissingBeforeHookRequest = missingAcceptedDYLuminosityConventionAuthority`
and
`firstMissingAfterHookRequest = missingAcceptedDYLuminosityConventionAuthority`;
it does not construct an authority value.

W4Docs inspection also found only same-name, constructorless intake surfaces
such as
`DASHI.Physics.Closure.AcceptedDYLuminosityConventionAuthorityReceipt`; those
do not inhabit the canonical `W4ZAdequacyReceipt` authority type and currently
record an insufficient/missing external provider answer.

Required hook signature:

```text
policyHook : ProviderAuthorityPacket -> AcceptedDYLuminosityConventionAuthority
policyHookWithBasis : W4PublicSourceAuthorityBasis -> ProviderAuthorityPacket -> AcceptedDYLuminosityConventionAuthority
zAdequacyConsumer : AcceptedDYLuminosityConventionAuthority -> W4 accepted m_i/d_i/ell_i/sigma_i inputs -> W4ZAdequacyReceipt
```

Both outputs must be the canonical
`DASHI.Physics.Closure.W4ZAdequacyReceipt` types, not W4-local shadow records.
The hook would become token-producing only if governance adds a W4-scoped,
non-postulated hook whose result type is the exact constructorless
`AcceptedDYLuminosityConventionAuthority` type, or if the authority owner module
adds a real constructor under an accepted receipt.

## Closure Route Audit

The current canonical audit is:

```text
DASHI.Physics.Closure.W4ZAdequacyReceipt.canonicalW4AuthorityClosureRouteAudit
```

It preserves CMS-SMP-20-003 / HEPData as public evidence, but explicitly rejects
three non-closing routes:

- public-source self-issued W4 authority;
- local `postulate` to `record` rewrite without owner/governance approval;
- W4-local shadow records that do not inhabit the canonical constructorless
  authority type.

The only accepted closure route is an exact provider/governance hook returning
`DASHI.Physics.Closure.W4ZAdequacyReceipt.AcceptedDYLuminosityConventionAuthority`,
or an owner-approved constructor in that canonical module.

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
missingW4ZAdequacyConsumer
missingAcceptedPerBinLuminosityVector
missingInternalDiagonalConvention
missingLeptonChannelCombineConvention
missingZAndBelowZAnchorBinding
missingProviderIdentityAndDate
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
internalStrictInequalityDischarged = true
```

No W4 adequacy, physical calibration, matter/stress-energy interface, GR, or
paper claim follows from this request.

Exact remaining blocker:

```text
before policy-hook request: missingAcceptedDYLuminosityConventionAuthority
after policy-hook request:  missingAcceptedDYLuminosityConventionAuthority
missingAcceptedDYLuminosityConventionAuthority
missingW4ZAdequacyConsumer
missingW4ExternalAuthorityTokenConstructor
missingTokenProducingPolicyHookForPublicCMSPaperAndHEPData
```

The strict inequality `9566 > 9000` is discharged internally by
`W4ResponseMatrixAcceptanceCandidateReceipt.scaledDecimalStrictGreaterThan9566over9000`.
That witness is non-promoting. Even after a policy hook or constructor exists,
W4 still requires the accepted per-bin luminosity vector, W4ZAdequacy consumer,
diagonal/channel/anchor conventions, and provider/date metadata before any W4
adequacy receipt can be considered.

The diagonal-convention consumer may record local diagonal arithmetic and a
non-promoting strict-inequality witness, but it does not alter the external
authority blocker. Its authority before/after hook fields remain
`missingAcceptedDYLuminosityConventionAuthority`.

Current audit result:

```text
public evidence preserved: true
exact accepted authority available here: false
postulate-to-record rewrite authorized here: false
```
