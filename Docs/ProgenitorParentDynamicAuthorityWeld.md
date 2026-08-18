# Progenitor / Parent Dynamic Authority Weld

This note records the action-facing extension of the parent/progenitor hyperfabric. It deliberately reuses existing DASHI dynamic-safety, policy-safety, non-factorability, provenance-reopening, plural-observer, and diachronic-authority kernels rather than adding another parent-specific foundation.

## 1. Public parent slots do not factor authority routing

`ProgenitorParentAuthorityRoutingNonfactorabilityExact.agda` uses the existing `IntersectionalNonFactorability` criterion on the literal parent carrier.

The anonymous IVF donor and adoptive parent both project to `P8810`, but the witness authority router sends them to different routes:

- anonymous donor -> `noParentalAuthorityRoute`;
- adoptive legal parent -> `legalParentDecisionRoute`.

Therefore no function on the Wikidata slot alone can reproduce the fine authority router:

`routeParentAuthority != interpretSlot o projectParentSlot`.

This strengthens `parentSlotDoesNotDetermineParentSemantics`: the lost distinction can be action-relevant, not merely descriptive.

## 2. Consumer-relative future safety

`ProgenitorParentObserverFutureSafetyExact.agda` instantiates the existing `DynamicalQuotientSafety`, `PluralConsumerProjectionSafety`, and `PolicyRelativeProjectionSafety` cores.

Two current states share the same public `P8810`-like observation. Under the same admissible `resolveCurrentAuthority` action, their authority-sensitive future observations differ. This is an exact `TerminalisationDefect`.

The public registry consumer is dynamically safe because it intentionally sees a constant public surface. The authority-decision consumer is not dynamically safe. Hence safety for the public registry consumer cannot be promoted to plural safety.

The policy-relative strengthening uses one coarse policy which selects the same resolution action for both collapsed states and constructs a `PolicyExposedQuotientDefect`. Thus the coarse parent surface is unsafe as the decision carrier for that authority policy.

This keeps the established DASHI distinction:

`static slot adequacy != consumer-relative future safety != policy-relative safety`.

## 3. Diachronic parent/caregiver authority

`ProgenitorParentDiachronicAuthorityFibreExact.agda` imports `DASHI.Governance.DiachronicDelegatedAuthorityBoundary` directly.

The parent relation is retained while current delegated authority is revoked. The imported laws remain intact:

- revocation terminates prospective authority without historical erasure;
- historical evidence does not restore authority;
- new discretionary action after revocation requires fresh authorisation;
- unavoidable continuation does not create a new mandate;
- supporter status cannot self-authorise override.

Authority is therefore treated as time/scope-sensitive state rather than as a permanent consequence of the `parent` label.

## 4. Exact reopening makes the residual a fine-fibre coordinate

`ProgenitorParentResidualDynamicsExact.agda` constructs a literal `ProvenanceBearingQuotient` for the parent fibre core:

- coarse surface: Wikidata parent slot;
- exact residual: `RelationVector`;
- reopening: slot level + relation residual -> `ParentCarrier`.

It proves exact reopening and therefore:

`same surface + same residual -> same fine parent carrier`.

Consequently, any nontrivial hidden transition at fixed public slot must move the residual. The existing legal-finalisation hidden transition is the canonical witness, and donor disclosure-state change gives a second witness.

This is the parent specialization of the generic receipt-dynamics theorem developed independently on PR #584. The parent branch does not duplicate PR #584's generic theorem layer; it proves the source-native application against the existing canonical quotient contract.

The receipt remains proof-relevant state, not semantic-erasure or disclosure authority.

## 5. Family agency is not parental sovereignty

`ProgenitorParentAllyshipAuthorityBridgeExact.agda` cross-pollinates two older repo lanes:

- `ParentAllyshipMultiObserverBridge`: parent expertise may count as evidence, child voice remains distinct, and no observer surface equals the whole system;
- `DiachronicDelegatedAuthorityBoundary`: support cannot self-authorise override.

The combined boundary is:

`family expertise/agency != canonical whole-system view != unlimited override authority`.

This is the formal counterpart of the education-policy distinction between supporting family agency and turning parenthood into epistemic or political sovereignty.

## 6. Relationship to observer refinement and PR #584

PR #581 already contains the static observer-refinement and fibre-dynamics cores needed by the parent ontology. PR #584 independently owns the generic bridges from observer refinement to future-language safety and from hidden fibre motion to receipt motion.

This tranche therefore avoids another generic core and instead supplies concrete parent witnesses that can later be discharged through those generic bridges when the stacks converge.

The resulting workflow is:

`concrete collision -> smallest source-native refinement -> routing/future-safety test -> exact residual retention -> authority/disclosure boundary`.

The operative invariant is:

> A coarse relation is acceptable only for the distinctions, consumers, actions, and future horizons that it demonstrably preserves.
