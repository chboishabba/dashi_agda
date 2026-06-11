# DASHI Governance Self-Issuance Policy

Date: `2026-05-13`
Status: `governance policy surface; non-promoting until consumed by a typed receipt`
Owner: `Lane-1 W2/W3 authority governance`

This policy states when DASHI governance may self-issue bounded authority tokens
and when an external countersignature remains required.

It does not populate, construct, or imply any W2 or W3 token by itself. A token
may be constructed only by a later typed receipt that names this policy, names
the exact token, names the exact evidence packet, and satisfies the audit and
revocation conditions below.

## Policy Fork

| Evidence class | Governance ruling | Countersignature rule |
|---|---|---|
| `refl-proved-internal` | Self-issuance is allowed for a bounded internal token when the evidence is a repo-local definitional/propositional equality proof or an inhabited internal receipt whose dependencies are all repo-local. | External countersignature is not required. |
| `public-doi-frozen-commit` | Self-issuance is allowed for a bounded empirical authority token when public DOI-bound evidence, frozen commit, artifact digest, checksum binding, comparison law, and non-collapse/audit witness are all recorded and reproducibly checked. | External countersignature is not required unless a consumer gate demands one. |
| `private-provider`, `licensed`, `ambiguous-provenance`, `non-reproducible`, or `policy-contested` | Self-issuance is not allowed. | External countersignature is required. |

Default for any unlisted class:

```text
selfIssuanceAllowed = false
externalCountersignatureRequired = true
```

## Required Self-Issuance Receipt Fields

A later self-issuance receipt must include:

```text
policy = Docs/DASHIGovernanceSelfIssuancePolicy.md
evidenceClass = refl-proved-internal | public-doi-frozen-commit
tokenName = exact token being constructed
laneScope = exact bounded W2/W3 lane scope
evidencePacket = exact file/artifact list
frozenCommit = exact commit hash, when empirical or runner-dependent
artifactDigests = exact SHA-256 values, when artifacts are consumed
publicAuthorityRefs = DOI/table/provider refs, when public evidence is consumed
comparisonOrProofLaw = exact law consumed by the token
nonCollapseOrNoOverreachWitness = exact witness
auditLog = exact validation commands or transcript
revocationConditions = named conditions below
```

Missing any required field means the token remains constructorless or
non-populated.

## Revocation Conditions

Any self-issued W2/W3 token must be revoked or marked suspended if one of these
conditions is later recorded:

- a public DOI, table id, payload checksum, or artifact digest mismatch;
- a frozen commit mismatch;
- a failed reproduction of the stated proof, runner, semantic match, or
  comparison law;
- a later accepted external authority rejects the evidence packet;
- the token is used outside its named bounded scope;
- the non-collapse/no-overreach witness is invalidated;
- a dependency receipt is withdrawn, superseded, or found to have imported an
  unstated authority assumption;
- governance records that the evidence class was misclassified.

Revocation is monotone at the policy layer: a revoked token cannot be silently
reinstated. A replacement token requires a new receipt with a new audit log.

## Audit Conditions

Before a self-issued token can be consumed downstream, an audit surface must
record:

```text
policyBranch = self-issuance
evidenceClass = refl-proved-internal | public-doi-frozen-commit
tokenNameMatchesConsumer = true
scopeBounded = true
allRequiredFieldsPresent = true
revocationConditionsNamed = true
validationCommandsRecorded = true
noOverreachClausesRecorded = true
```

For `public-doi-frozen-commit`, the audit must also record:

```text
publicDOIsRecorded = true
canonicalPayloadChecksumsRecorded = true
frozenCommitRecorded = true
artifactDigestsRecorded = true
semanticOrNumericalChecksRecorded = true
```

For `refl-proved-internal`, the audit must record the exact repo-local proof
surface and confirm that the consumed proof is not merely a postulate, request
surface, or candidate route.

## No-Overreach Clauses

Self-issuance is always bounded to the named token and evidence packet. It does
not promote:

- broad W2 closure beyond the named W2 receipt;
- broad W3 empirical adequacy beyond the named W3 receipt;
- W4/W5 Drell-Yan convention or physical-unit authority;
- W8 origin;
- W9 cancellation pressure;
- G5 empirical adequacy as a whole;
- full physics unification.

## W2/W3 Ruling

For W2/W3 governance, this policy adopts the following ruling:

```text
reflProvedInternalSelfIssuanceAllowed = true
publicDOIFrozenCommitSelfIssuanceAllowed = true
externalCountersignatureRequiredForOtherClasses = true
tokensConstructedByThisPolicy = false
```

The policy is permissive only at the governance layer. A W2 or W3 authority
token is still absent until a later typed receipt explicitly consumes this
policy and satisfies all required fields, audit conditions, revocation
conditions, and no-overreach clauses.

## Typed Hook Boundary

The smallest admissible typed hook for this policy is a receipt/request surface
that consumes:

- this policy document;
- the exact W2 or W3 evidence packet;
- the current audit, revocation, and no-overreach clauses;
- the exact token name and lane scope;
- the current typed blocker state.

Such a hook may record that the policy has been consumed as typed governance
evidence. It may not fabricate a constructorless authority token. A hook is
token-producing only when the current Agda surface already provides either an
explicit token constructor or a non-postulated policy hook whose result type is
the exact token type being consumed by the downstream receipt.

Current W2/W3 ruling:

```text
typedPolicyHookRequestSurfaceAllowed = true
tokenProducingHookAuthorizedNow = false
W2NaturalP2ConvergencePromotionAuthorityTokenConstructed = false
W3AcceptedEvidenceAuthorityTokenConstructed = false
```

For W2, the token-producing hook remains unauthorized because
`NaturalP2ConvergencePromotionAuthorityToken` is constructorless and the
natural/p2 bridge, coherence, carrier transport, carrier-general convergence,
and realization-uniform rate payloads remain uninhabited. For W3, the
token-producing hook remains unauthorized because the current intake/response
surfaces still record absent self-issuance authority, absent provider canonical
table-checksum binding, and absent accepted authority-token response over the
staged `t43`/`t44` payloads.
