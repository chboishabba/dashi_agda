# Federated Subsidiarity Governance Design

## Intent

Formalise the transcript's structural governance claim without promoting it into an empirical or political conclusion. The transcript motivates a failure mode in globally coupled consensus systems and an alternative architecture based on local autonomy plus federation. The formal layer must separate transcript-derived hypotheses from DASHI derivations.

## Existing owners reused

- `DASHI.Governance.AuthorityMandateCore`: scoped, recallable, reviewable, non-alienating mandate semantics. It does not create popular legitimacy.
- `DASHI.Governance.SituatedConstituency`: place/time/institution/axis-qualified constituency carrier. It does not claim an exhaustive axis list or create representative authority.

The new owner must not duplicate those semantics.

## New owner

`DASHI/Governance/FederatedSubsidiarityGovernanceExact.agda`

It introduces:

1. `IssueScope` with local, boundary and federation-wide constructors.
2. `FederatedGovernance` carrying communities, agents, issues, membership, participation and issue scope.
3. `SubsidiarityWitness` stating that participation in a local issue requires membership in the affected community.
4. A theorem that a non-member cannot participate in a local issue under a subsidiarity witness.
5. Coordination-load decomposition into local and boundary load, with an exact upper-bound theorem for the defined federated load.
6. A minimal `CommunityGuarantee` / `ComposablePair` carrier showing that local guarantees can be retained under an explicitly compatible interface without inventing compatibility.
7. A transition system with create/join/exit/split/federate/share-infrastructure transition kinds and reflexive-transitive reachability.
8. A `ViabilityEnvelope` separating governance, ecological/resource and basic-needs predicates. No thresholds or empirical constants are invented.
9. Explicit firewalls: formalisation does not prove decentralisation is empirically superior; consensus is not definitionally democracy; federation is not definitionally legitimate; ecological viability is not inferred from governance form.

## Structural claims proved

The owner may prove only consequences of explicit definitions/witnesses:

- local participation exclusion for non-members;
- reflexive and one-step reachability;
- exact federated-load decomposition;
- retention of paired guarantees when a `ComposablePair` contains both guarantee witnesses and an explicit compatibility witness.

## Source boundary

The transcript supplies motivation and the governance-scaling problem statement. It does not by itself supply quantitative scaling laws, empirical coordination-cost measurements, ecological thresholds, or evidence that the proposed alternative dominates all other governance forms. Those remain external hypotheses/instantiations.

## Regression owner

`DASHI/Governance/FederatedSubsidiarityGovernanceRegression.agda` will instantiate a two-community finite example and verify:

- a local issue scoped to community A excludes an agent known not to belong to A;
- one transition is reachable;
- the federated load is exactly local load plus boundary load;
- the canonical authority-boundary booleans remain non-promoting.

## Aggregation

Import both new modules from `DASHI/Governance/Everything.agda`.