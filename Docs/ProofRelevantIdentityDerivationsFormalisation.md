# Proof-Relevant Identity Fibres and Factor Derivations

## Runtime correspondence

This formalisation corresponds to SensibLaw migrations 069–073. It extends the
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

Identity evidence is also indexed by kind. Constructors exist for evidence
such as apposition, proper-name expansion, title/role closure, uniquely resolved
typed demands and external alignment. Deliberately no projection constructor
exists for:

```text
paragraphCoScopeEvidence
lexicalProximityEvidence
```

which yields the structural impossibility results:

```text
IdentityProjectionPermission paragraphCoScopeEvidence -> bottom
IdentityProjectionPermission lexicalProximityEvidence -> bottom
```

A canonical entity is therefore a base over which immutable local objects are
fibred rather than a destructive merge target.

`IdentityFibreMember` carries the admitted witness explicitly and requires
proofs that the local fibre object equals the witness source and that the
canonical entity identity equals the witness target. Fibre membership therefore
cannot float free of its proof object.

## Candidate multiplicity

Identity projection reuses the sparse frontier witness multiplicity:

```text
noWitness
oneWitness
severalWitnesses
```

`IdentityProjection` has a constructor only at `oneWitness`. No witness and
ambiguous witnesses have empty elimination proofs, matching the PostgreSQL
`resolved_unique` gate.

## Proof-relevant substitution

`ProofRelevantFactorDerivations.agda` defines `IdentitySubstitutionProof` with:

- premise factor;
- source local object;
- target canonical entity;
- admitted identity witness;
- proof that the source object matches the witness source; and
- proof that the target entity matches the witness target.

A derived argument similarly retains both the source object and the admitted
witness. `IdentitySubstitutionDerivation` retains the original premise factor
and carries an equality showing that the retained premise is the one named by
the proof.

This corresponds to the runtime rule:

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

`FactorCompositionCandidate` additionally carries a numeric rank/limit witness.

Composition permission is indexed by authority:

```text
candidateOnlyAuthority
explicitDomainRuleAuthority
```

Only the explicit-domain-rule authority has a constructor. Therefore:

```text
CompositionPermission candidateOnlyAuthority -> bottom
```

and the `DerivedProposition factorComposition` constructor requires an
`AdmittedFactorComposition`, which itself requires explicit rule permission.

This proves the distinction between structural composability and semantic
entailment: a shared participant, even under witnessed identity, cannot silently
become a new proposition.

## Retraction correspondence

SensibLaw migrations 072–073 recompute current document-derived witness
admission and rebuild current Level-3 identity substitutions. Migration 073 also
makes explicit external-authority witness admission and retraction immediately
refresh the affected document's substitution and composition frontiers.

The Agda authority split makes that safe: local factors and witness evidence are
separate values from the permission that admits them to a current projection.
Retraction therefore does not require rewriting the local evidence object.

External-world alignment remains a distinct authority path. No local or
corpus-derived constructor can manufacture `WorldCanonicalPermission`.

## Aggregate

Both modules are publicly imported by:

```text
DASHI.Cognition.PNF.NumericPNFHyperfabricEverything
```

and included in the focused Agda 2.9 workflow.
