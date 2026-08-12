module DASHI.Governance.ProvenancePolicyTransport where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Provenance-to-policy transport.
--
-- Provenance is not intrinsically fascistic or antifascistic.  Repair law,
-- historical explanation, restitution and ordinary adjudication all need to
-- operationalise provenance.  The normative/structural question is which
-- proposition-local route transports which provenance into which action.
------------------------------------------------------------------------

record ProvenancePolicySystem : Set₁ where
  field
    Actor : Set
    Provenance : Set
    PresentEvidence : Set
    Classification : Set
    Action : Set
    Defeater : Set

    provenance : Actor → Provenance
    classify : PresentEvidence → Actor → Classification
    route : Provenance → PresentEvidence → Classification → Action
    revise : Defeater → Classification → Classification

open ProvenancePolicySystem public

data ProvenanceRouteKind : Set where
  evidentiaryRoute : ProvenanceRouteKind
  reparativeRoute : ProvenanceRouteKind
  coerciveRoute : ProvenanceRouteKind
  representationalRoute : ProvenanceRouteKind

------------------------------------------------------------------------
-- Support-local action law.
------------------------------------------------------------------------

record PropositionLocalPolicy
    (S : ProvenancePolicySystem) : Set₁ where
  field
    ActionSupport : Actor S → Action S → Set
    supportedRoute :
      (actor : Actor S) →
      (evidence : PresentEvidence S) →
      ActionSupport actor
        (route S
          (provenance S actor)
          evidence
          (classify S evidence actor))

open PropositionLocalPolicy public

------------------------------------------------------------------------
-- Collective-guilt transport is never manufactured by group adjacency.
------------------------------------------------------------------------

record CollectiveMembershipBoundary
    (S : ProvenancePolicySystem) : Set₁ where
  field
    Group : Set
    member : Actor S → Group → Set
    Responsible : Actor S → Set
    MembershipAloneTransfersResponsibility : Set
    membershipAloneCannotTransfer :
      MembershipAloneTransfersResponsibility → ⊥

open CollectiveMembershipBoundary public

------------------------------------------------------------------------
-- Defeater/revision liveness.
--
-- This does not require every defeater to reverse a classification.  It
-- requires a proposition-level witness when an application claims a
-- classification is genuinely revisable under a named defeater.
------------------------------------------------------------------------

record DefeaterLive
    (S : ProvenancePolicySystem)
    (classification : Classification S)
    (defeater : Defeater S) : Set where
  field
    revised : Classification S
    revisionExact : revise S defeater classification ≡ revised
    revisionIsLive : classification ≡ revised → ⊥

open DefeaterLive public

------------------------------------------------------------------------
-- Operator witnesses.  These are independent coordinates, not a total
-- political label.  Concrete empirical applications need separate evidence.
------------------------------------------------------------------------

record ErasureWitness (S : ProvenancePolicySystem) : Set₁ where
  field
    actor : Actor S
    ProvenanceDistinction : Set
    distinctionLost : ProvenanceDistinction

record WeaponisationWitness (S : ProvenancePolicySystem) : Set₁ where
  field
    actor : Actor S
    baselineEvidence activatedEvidence : PresentEvidence S
    CoerciveExpansion : Action S → Action S → Set
    expansion :
      CoerciveExpansion
        (route S (provenance S actor) baselineEvidence
          (classify S baselineEvidence actor))
        (route S (provenance S actor) activatedEvidence
          (classify S activatedEvidence actor))

record CollectiveGuiltWitness
    (S : ProvenancePolicySystem)
    (B : CollectiveMembershipBoundary S) : Set₁ where
  field
    source target : Actor S
    group : Group B
    sourceMember : member B source group
    targetMember : member B target group
    sourceResponsible : Responsible B source
    inheritedTransferAttempt :
      MembershipAloneTransfersResponsibility B

record AsymmetricRoutingWitness (S : ProvenancePolicySystem) : Set₁ where
  field
    left right : Actor S
    leftEvidence rightEvidence : PresentEvidence S
    EquivalentEvidence : PresentEvidence S → PresentEvidence S → Set
    equivalentEvidence : EquivalentEvidence leftEvidence rightEvidence
    RouteAsymmetry : Action S → Action S → Set
    asymmetric :
      RouteAsymmetry
        (route S (provenance S left) leftEvidence
          (classify S leftEvidence left))
        (route S (provenance S right) rightEvidence
          (classify S rightEvidence right))

------------------------------------------------------------------------
-- Antifascistic certificate family: recoverability/locality/revision are
-- independently supplied; there is no claim that one global inverse settles
-- every political question.
------------------------------------------------------------------------

record AntifascisticCertificate (S : ProvenancePolicySystem) : Set₁ where
  field
    localPolicy : PropositionLocalPolicy S
    collectiveBoundary : CollectiveMembershipBoundary S
    ReopeningReceipt : Set
    reopeningReceipt : Actor S → ReopeningReceipt
    CounterevidenceCase : Set
    counterevidenceRemainsAdmissible : CounterevidenceCase → Set

open AntifascisticCertificate public

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

data ProvenancePolicyPromotion : Set where
  provenanceIsEvidence : ProvenancePolicyPromotion

data ProvenanceAutomaticallyLicensesCoercion : ProvenancePolicyPromotion → Set where

provenanceDoesNotAutomaticallyLicenseCoercion :
  ProvenanceAutomaticallyLicensesCoercion provenanceIsEvidence → ⊥
provenanceDoesNotAutomaticallyLicenseCoercion ()

record ProvenancePolicyBoundary : Set where
  constructor provenancePolicyBoundary
  field
    provenanceOperationalisationIsNeutral : Bool
    provenanceOperationalisationIsNeutralIsTrue :
      provenanceOperationalisationIsNeutral ≡ true
    provenanceAutomaticallyLicensesCoercion : Bool
    provenanceAutomaticallyLicensesCoercionIsFalse :
      provenanceAutomaticallyLicensesCoercion ≡ false

canonicalProvenancePolicyBoundary : ProvenancePolicyBoundary
canonicalProvenancePolicyBoundary =
  provenancePolicyBoundary true refl false refl
