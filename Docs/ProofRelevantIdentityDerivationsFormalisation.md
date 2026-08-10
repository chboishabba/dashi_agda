# Proof-Relevant Identity Fibres and Factor Derivations

## Runtime correspondence

This formalisation corresponds to SensibLaw migrations 069–074. It extends the
existing sparse-frontier model without creating a second semantic graph.

The runtime path is:

```text
local observations
-> local factors
-> sparse frontiers
-> typed demand resolution
-> proof-relevant identity witnesses
-> witnessed identity substitutions
-> bounded factor-composition candidates
-> root-only publication
```

## Identity is a witnessed projection

`ProofRelevantIdentityFibres.agda` separates four authority classes:

```text
surfaceLocal
documentDerived
corpusDerived
externalAuthority
```

Only `externalAuthority` has a `WorldCanonicalPermission` constructor. The
empty-pattern theorems prove that local, document-derived and corpus-derived
identity cannot by themselves assert a world-canonical entity.

Identity evidence is indexed by kind. Constructors exist for evidence such as
apposition, proper-name expansion, title/role closure, uniquely resolved typed
demands and external alignment. Deliberately no projection constructor exists
for:

```text
paragraphCoScopeEvidence
lexicalProximityEvidence
```

which yields:

```text
IdentityProjectionPermission paragraphCoScopeEvidence -> bottom
IdentityProjectionPermission lexicalProximityEvidence -> bottom
```

A canonical entity is therefore a base over which immutable local objects are
fibred rather than a destructive merge target.

## Projection integrity

`IdentityProjection` is indexed by the **exact admitted witness**. Its unique
constructor requires proofs that:

```text
witnessCandidateCount = 1
witnessAuthority = canonicalAuthority(witnessTargetEntity)
```

and inhabits only the `oneWitness` multiplicity index. Therefore neither
`noWitness` nor `severalWitnesses` can project identity, and authority agreement
is part of the proof rather than an unrelated annotation.

`IdentityFibreMember` carries that admitted witness explicitly and requires
proofs that the local fibre object equals the witness source and that the
canonical entity identity equals the witness target. Fibre membership cannot
float free of its proof object.

This mirrors SensibLaw migration 074, which enforces candidate-count-one and
authority equality when an identity witness is marked accepted, repeats those
conditions in the current projection view, supersedes invalid historical
admissions, and purges stale Level-3 substitutions that are no longer backed by
a valid projection.

## Proof-relevant substitution

`ProofRelevantFactorDerivations.agda` defines `IdentitySubstitutionProof` with:

- premise factor;
- source local object;
- target canonical entity;
- admitted identity witness;
- proof that the source object matches the witness source; and
- proof that the target entity matches the witness target.

A derived argument similarly retains both the source object and admitted
witness. `IdentitySubstitutionDerivation` retains the original premise factor
and carries equality showing that the retained premise is the one named by the
proof.

```text
F(surface argument = o)
pi : o ==> E
----------------------- identity-substitution:v1
F(entity argument = E)
```

without modifying `F`.

## Factor composition remains candidate-only

A factor bridge is either:

- an exact local object; or
- a `WitnessedEntityBridge` carrying two admitted witnesses, proofs that both
  target the same canonical entity, and proof that their identity authority
  classes are equal.

`FactorCompositionCandidate` also carries a numeric rank/limit witness.

Composition permission is indexed by authority:

```text
candidateOnlyAuthority
explicitDomainRuleAuthority
```

Only explicit-domain-rule authority has a constructor. Therefore:

```text
CompositionPermission candidateOnlyAuthority -> bottom
```

and `DerivedProposition factorComposition` requires an
`AdmittedFactorComposition` carrying explicit rule permission. Shared
participants or witnessed identity alone cannot silently become entailments.

## Retraction correspondence

SensibLaw migrations 072–073 recompute document-derived witness admission and
rebuild current Level-3 identity substitutions. Explicit external-authority
witness admission and retraction immediately refresh the affected document's
substitution and composition frontiers.

The formal authority split makes that safe: immutable local evidence, witness
evidence, and permission/admission are separate values. Retraction changes
current authority rather than rewriting historical evidence.

External-world alignment remains a distinct authority path. No local or
corpus-derived constructor can manufacture `WorldCanonicalPermission`.

## Aggregate

Both modules are publicly imported by:

```text
DASHI.Cognition.PNF.NumericPNFHyperfabricEverything
```

and included in the focused Agda 2.9 workflow.
