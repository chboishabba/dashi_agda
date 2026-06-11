# W2/W3 Authority Governance Fork

Date: `2026-05-13`
Status: `policy surface; candidate-only; non-promoting`
Owner: `Lane-1 W3/W2 authority governance`

This surface formalizes the governance fork for W2/W3 authority handling after
canonical public evidence has been staged and locally checked.

Governing policy:

```text
Docs/DASHIGovernanceSelfIssuancePolicy.md
```

It does not construct:

- `W3AcceptedEvidenceAuthorityToken`;
- any W2 empirical-authority token;
- a downstream W3 consumable anchor;
- broad empirical adequacy;
- physics-unification closure.

## Fork Question

When public canonical evidence is locally staged, hash-bound, and semantically
matched against the repo cache, governance must choose one authority rule:

| Policy branch | Meaning | Token consequence |
|---|---|---|
| `external-countersignature-required` | Public canonical evidence is necessary but not sufficient. A provider, reviewer, repo-governance authority, or other explicitly accepted countersigner must accept the packet. | No local `W3AcceptedEvidenceAuthorityToken` construction. The token remains blocked until the countersignature is present. |
| `self-issuance-under-public-canonical-evidence` | Governance authorizes the repo to treat public DOI-bound evidence plus frozen commit, artifact digest, checksum binding, comparison law, and reproducible checks as sufficient authority for a bounded token. | Token construction becomes policy-permitted only for the exact named packet and only after every self-issuance, audit, revocation, and no-overreach condition in `Docs/DASHIGovernanceSelfIssuancePolicy.md` is satisfied. |
| `self-issuance-for-refl-proved-internal` | Governance authorizes self-issuance for repo-local `refl`/propositional-equality/internal receipts whose dependencies are all repo-local and not candidate-only. | Token construction becomes policy-permitted only for the exact internal token named by a typed receipt and after audit/revocation clauses are recorded. |

Current governance ruling:

```text
reflProvedInternalSelfIssuanceAllowed = true
publicDOIFrozenCommitSelfIssuanceAllowed = true
externalCountersignatureRequiredForOtherClasses = true
authorityTokenConstructedHere = false
```

## Current Inputs

W3 currently has a local candidate pass:

```text
artifact = logs/research/w3_frozen_3205d74_t43_comparison_20260513.json
artifactSha256 = 92b61032c06cb4d00d22e00bf9e280b47806f9ebf18f012f5b82a41b0afae238
chi2/dof = 2.1565191176275618
status = candidate-pass-no-authority-token
```

The active W3 ratio payloads are locally staged and semantically checked:

```text
t43 canonical JSON sha256 = 5cfefe5a5a99c415f9225a3515383e8ce5e9a874861ff6c5fc08365871bfd340
t44 canonical JSON sha256 = 2dfa2abe120981f1f8379d95c8d6e0362394c6f6c8fed01dd45fc76a3e2b660b
t43 semantic match = 18/18
t44 semantic match = 324/324
```

These facts are evidence inputs. They are not, by themselves, the governance
decision.

## Branch A: External Countersignature Required

This branch preserves the existing W3 posture.

Required promotion condition:

```text
acceptedCountersignaturePresent = true
```

The countersignature must bind:

- provider or governance authority identity;
- decision timestamp;
- DOI/table provenance for HEPData `t43` and `t44`;
- CMS-SMP-20-003 and CMS paper provenance;
- frozen commit;
- comparison artifact digest;
- canonical payload checksums or provider-equivalent immutable records;
- comparison law;
- covariance source;
- non-collapse witness;
- exact accepted/rejected/insufficient decision.

Under this branch, public canonical evidence can narrow the gap but cannot
replace the countersignature.

## Branch B: Self-Issuance Under Public Canonical Evidence

This branch is governance-allowed by
`Docs/DASHIGovernanceSelfIssuancePolicy.md`, but no W2/W3 token is populated by
this document. A later typed receipt must still name the exact token and exact
evidence packet.

Required activation condition:

```text
selectedPolicyBranch = self-issuance-under-public-canonical-evidence
policyReceiptNamesExactToken = true
policyReceiptNamesExactEvidencePacket = true
policyReceiptNamesResponsibleAuthority = true
policyReceiptStatesNoExternalCountersignatureNeeded = true
revocationConditionsNamed = true
auditConditionsRecorded = true
```

Required evidence preconditions:

```text
canonicalPublicPayloadsStaged = true
canonicalPayloadChecksumsRecorded = true
semanticMatchAgainstLocalCache = true
frozenComparisonArtifactDigestMatches = true
comparisonLawFrozen = true
nonCollapseWitnessRecorded = true
scopeIsBoundedToW3T43 = true
```

Required no-overreach clauses:

```text
doesNotPromoteW2BeyondItsOwnReceipts = true
doesNotPromoteW4OrW5 = true
doesNotPromoteW8OrW9 = true
doesNotClaimBroadEmpiricalAdequacy = true
doesNotClaimCompletePhysicsUnification = true
```

Only when both the activation condition and every evidence precondition are
present may a later worker propose a bounded self-issued W3 authority token by
typed receipt. This document itself does not construct the token.

## Branch C: Self-Issuance For Refl-Proved/Internal Evidence

This branch is governance-allowed for W2/W3 surfaces only when the evidence is
repo-local and internally inhabited.

Required activation condition:

```text
selectedPolicyBranch = self-issuance-for-refl-proved-internal
evidenceClass = refl-proved-internal
tokenName = exact bounded W2/W3 token
internalProofSurfaceNamed = true
proofIsNotPostulateRequestOrCandidate = true
dependenciesAreRepoLocal = true
revocationConditionsNamed = true
auditConditionsRecorded = true
```

This branch cannot be used for public empirical evidence unless the packet also
qualifies under Branch B. It also cannot promote W2 or W3 beyond the exact
internal receipt named by the later typed token.

## W2 Relationship

W2 can supply local mathematical/dynamical receipts that make the W3 comparison
law meaningful. W2 cannot, by itself, decide the empirical authority branch.

Governance must keep these roles separate:

| Lane | Can supply | Cannot supply alone |
|---|---|---|
| W2 | Internal dynamics, naturalness, boundedness, or convergence receipts used by the comparison law. | W3 accepted empirical authority over public data. |
| W3 | Empirical packet, canonical payload binding, comparison artifact, non-collapse witness. | W2 mathematical closure or broader physics adequacy. |

## Current Decision Record

As of this surface:

```text
selectedGovernancePolicy = Docs/DASHIGovernanceSelfIssuancePolicy.md
reflProvedInternalSelfIssuanceAllowed = true
publicDOIFrozenCommitSelfIssuanceAllowed = true
externalCountersignatureRequiredForOtherClasses = true
W3AcceptedEvidenceAuthorityTokenConstructed = false
exactRemainingGovernanceGap =
  later typed receipt naming exact token, exact evidence packet,
  audit conditions, revocation conditions, and no-overreach clauses,
  or external accepted countersignature
```

Until that governance gap changes, all W2/W3 results remain candidate or
locally verified surfaces only.

## Governance Hook Decision

The typed interface change for this lane is obstruction/request-only:

```text
hookSurface =
  DASHI.Physics.Closure.W2W3GovernancePolicyHookRequest
typedPolicyEvidenceConsumed = true
tokenProducingHookAuthorizedNow = false
W2NaturalP2ConvergencePromotionAuthorityTokenConstructed = false
W3AcceptedEvidenceAuthorityTokenConstructed = false
```

This hook is allowed to consume the landed policy and the staged W2/W3 evidence
as typed governance inputs. It is not allowed to return either constructorless
authority token. A future token-producing hook must change the current typed
blocker state by supplying a real constructor or non-postulated hook for the
exact token type, plus every evidence, audit, revocation, and no-overreach
field required by `Docs/DASHIGovernanceSelfIssuancePolicy.md`.

The current W2 blocker is not only governance authority: even after a legitimate
authority token exists, W2 still needs natural/p2 bridge packaging, coherence
laws, carrier transport preserving convergence, and carrier-general
realization-uniform convergence receipts.

The current W3 blocker is not only public evidence availability: the staged
canonical `t43`/`t44` payloads are evidence inputs, while the intake and
provider-response surfaces still record no accepted authority-token response
and no provider canonical table-checksum binding.

## Worker B W3 Token Audit

Typed audit surface:

```text
DASHI/Physics/Closure/W3AcceptedEvidenceAuthorityTokenGovernanceObstruction.agda
logs/research/w3_authority_token_governance_obstruction_20260513.json
```

Result:

```text
policyBranch = public-doi-frozen-commit
boundedSelfIssuancePermittedByPolicy = true
W3AcceptedEvidenceAuthorityTokenConstructed = false
exactMissingConstructor =
  constructor for data W3AcceptedEvidenceAuthorityToken in
  DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate
exactMissingProviderField = Pack.missingAcceptedEvidenceAuthorityToken
exactTypedReceiptField = W3AcceptedEvidenceAuthorityTokenReceipt.authorityToken
```

The non-collapse witness script is not the first missing W3 item anymore: the
runner-side witness is represented by
`canonicalHEPDataW3T43RunnerPerBinNonCollapseReceipt`. The provider-grade
external non-collapse receipt remains absent, but the authority-token lane is
blocked first by the uninhabited token type and missing typed receipt field.
