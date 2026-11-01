# W2 Governance Token Constructor Obstruction

Date: `2026-05-13`
Status: `typed obstruction request; non-promoting`
Owner: `Worker A / W2 governance token lane`

This note records the result of inspecting the landed W2/W3 governance policy
against the current W2 token and receipt modules. The typed Agda surface is
`DASHI/Physics/Closure/W2GovernanceTokenConstructorObstruction.agda`.

## Decision

`Docs/DASHIGovernanceSelfIssuancePolicy.md` permits bounded self-issuance for
the `refl-proved-internal` evidence class, but it explicitly constructs no W2
or W3 token by itself. A later typed receipt must name the exact token, exact
evidence packet, audit conditions, revocation conditions, and no-overreach
clauses.

The current W2 Agda surface still defines:

```text
data NaturalP2ConvergencePromotionAuthorityToken : Set where
```

with no constructor. Therefore the policy does not yet provide a real
non-postulated `NaturalP2ConvergencePromotionAuthorityToken`.

## First Missing Constructor

The first missing Agda-level item is:

```text
NaturalP2ConvergencePromotionAuthorityToken constructor
```

or an equivalent typed governance-policy hook that inhabits that exact token
without postulates.

The exact typed interface is in:

```text
DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation
```

and currently has the constructorless shape:

```text
data NaturalP2ConvergencePromotionAuthorityToken : Set where
```

A valid governance hook would need result type exactly:

```text
NaturalP2ConvergencePromotionAuthorityToken
```

and must consume `Docs/DASHIGovernanceSelfIssuancePolicy.md` as typed policy
evidence, naming `tokenName = NaturalP2ConvergencePromotionAuthorityToken`,
`laneScope = W2 natural-p2-convergence`, the exact evidence packet, audit
conditions, revocation conditions, and no-overreach clauses. A prose ruling or
request packet is not this hook.

Until that constructor or hook exists, `NaturalP2ConvergencePromotionReceipt`
cannot be inhabited because its first required field is:

```text
promotionAuthority : NaturalP2ConvergencePromotionAuthorityToken
```

## Additional W2 Payload Still Missing

Even after a legitimate authority-token constructor exists, the promotion
receipt still requires non-candidate W2 payload fields already recorded by
`DASHI/Physics/Closure/NaturalP2ConvergencePromotionObligation.agda`:

- natural p2 bridge-or-obstruction packaging;
- naturality and p2 coherence carriers/laws;
- carrier transport preserving convergence;
- carrier-general convergence-rate receipt;
- realization-uniform convergence beyond the shift-flow carrier.

## Boundary

This obstruction does not change the governance policy. It consumes the policy
as permissive at the class level and records that class-level permission is not
an Agda inhabitant. No W2 promotion authority token or
`NaturalP2ConvergencePromotionReceipt` is constructed by this note or by the
Agda obstruction surface.
