module DASHI.Governance.MiddleEastProvenancePolicyRouting where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
import DASHI.Governance.IranUS2026RestitutionObservation as Iran

------------------------------------------------------------------------
-- Source-bounded Middle-East policy-routing application surface.
--
-- This module does not collapse Trump/US, Iran, Israel, Palestinians, Hamas,
-- or civilians into symmetric actors.  It formalises the rule-level questions
-- raised by the attached analysis: who is a negotiating subject, what
-- provenance supports which policy channel, whether civilian identity is
-- substituted for organisational/state responsibility, and whether repair is
-- treated as a right or merely as a consequence of bargaining leverage.
--
-- Source anchors supplied in the attached analysis (news sources; no DOI):
-- * Reuters, 10 August 2026, "Trump's Gaza plan hinges on Hamas disarmament,
--   Israeli withdrawals".
-- * Reuters reporting in 2026 on US/Israel/Iran ceasefire and negotiation
--   sequencing (carried through syndicated reporting in the attachment).
-- * ABC News, 18 June 2026, preliminary US-Iran memorandum/reconstruction.
--
-- These are empirical observation receipts only; the algebra below is DASHI's
-- structural formalisation and does not infer motive, guilt, legality, or a
-- total political label.
------------------------------------------------------------------------

reutersGazaReceipt : Iran.SourceReceipt
reutersGazaReceipt =
  Iran.sourceReceipt
    "Reuters"
    "Trump's Gaza plan hinges on Hamas disarmament, Israeli withdrawals"
    "10 August 2026"
    "news report; no DOI"

record MiddleEastRoutingSystem : Set₁ where
  field
    Actor : Set
    Event : Set
    Provenance : Set
    Evidence : Set
    Power : Set
    Claim : Set
    Policy : Set

    provenance : Actor → Provenance
    power : Actor → Power
    supports : Evidence → Claim → Set
    route : Actor → Provenance → Evidence → Policy

open MiddleEastRoutingSystem public

data SubjectStatus : Set where
  negotiatingSubject protectedSubject threatCarrier administrativeObject : SubjectStatus

data PolicyChannel : Set where
  recognition negotiation sanction militaryAttack reconstruction disarmament
  detention withdrawal aid compensation : PolicyChannel

record SubjectRouting (S : MiddleEastRoutingSystem) : Set₁ where
  field
    status : Actor S → SubjectStatus
    channel : Policy S → PolicyChannel

open SubjectRouting public

------------------------------------------------------------------------
-- Responsibility and civilian identity are distinct propositions.
------------------------------------------------------------------------

record ResponsibilityLocality (S : MiddleEastRoutingSystem) : Set₁ where
  field
    Civilian : Actor S → Set
    OrganisationMember : Actor S → Set
    StateActor : Actor S → Set
    ResponsibleFor : Actor S → Event S → Set

    civilianNonSubstitution :
      ∀ {civilian actor event} →
      Civilian civilian →
      ResponsibleFor actor event →
      Set

open ResponsibilityLocality public

-- No generic constructor promotes civilian/group identity to responsibility.
data CivilianIdentityAutomaticallyInheritsResponsibility
    {S : MiddleEastRoutingSystem}
    (R : ResponsibilityLocality S) : Set where

civilianIdentityDoesNotAutomaticallyInheritResponsibility :
  ∀ {S} {R : ResponsibilityLocality S} →
  CivilianIdentityAutomaticallyInheritsResponsibility R → ⊥
civilianIdentityDoesNotAutomaticallyInheritResponsibility ()

------------------------------------------------------------------------
-- Same rule is not same outcome.  Equivalent evidence must be processed by an
-- identity-independent rule schema while material power/injury remains data.
------------------------------------------------------------------------

record RoleEquivariantRouting (S : MiddleEastRoutingSystem) : Set₁ where
  field
    swapRole : Actor S → Actor S
    swapEvidence : Evidence S → Evidence S
    EquivalentPolicyRule : Policy S → Policy S → Set

    routeEquivariant :
      ∀ actor evidence →
      EquivalentPolicyRule
        (route S actor (provenance S actor) evidence)
        (route S
          (swapRole actor)
          (provenance S (swapRole actor))
          (swapEvidence evidence))

open RoleEquivariantRouting public

data RoleEquivarianceAutomaticallyEqualisesPower
    {S : MiddleEastRoutingSystem}
    (R : RoleEquivariantRouting S) : Set where

roleEquivarianceDoesNotEqualisePower :
  ∀ {S} {R : RoleEquivariantRouting S} →
  RoleEquivarianceAutomaticallyEqualisesPower R → ⊥
roleEquivarianceDoesNotEqualisePower ()

------------------------------------------------------------------------
-- Repair entitlement and leverage are independent coordinates.
------------------------------------------------------------------------

record RepairLeverageSeparation (S : MiddleEastRoutingSystem) : Set₁ where
  field
    RepairEntitlement : Actor S → Set
    BargainingLeverage : Actor S → Set
    actor : Actor S
    repairEntitlement : RepairEntitlement actor
    LeverageStatus : Set
    leverageStatus : LeverageStatus

open RepairLeverageSeparation public

data RepairEntitlementAutomaticallyMeansHighLeverage
    {S : MiddleEastRoutingSystem}
    (R : RepairLeverageSeparation S) : Set where

data HighLeverageAutomaticallyCreatesRepairEntitlement
    {S : MiddleEastRoutingSystem}
    (R : RepairLeverageSeparation S) : Set where

repairRightDoesNotAutomaticallyMeanLeverage :
  ∀ {S} {R : RepairLeverageSeparation S} →
  RepairEntitlementAutomaticallyMeansHighLeverage R → ⊥
repairRightDoesNotAutomaticallyMeanLeverage ()

leverageDoesNotAutomaticallyCreateRepairRight :
  ∀ {S} {R : RepairLeverageSeparation S} →
  HighLeverageAutomaticallyCreatesRepairEntitlement R → ⊥
leverageDoesNotAutomaticallyCreateRepairRight ()

------------------------------------------------------------------------
-- Empirical boundary carried from the attachment: policy roles can change
-- over time, so enemy/threat classification is not an immutable identity.
------------------------------------------------------------------------

record MiddleEastObservationBoundary : Set where
  constructor middleEastObservationBoundary
  field
    rolesAreTimeRevisable : Bool
    rolesAreTimeRevisableIsTrue : rolesAreTimeRevisable ≡ true
    sameRuleRequiresSameOutcome : Bool
    sameRuleRequiresSameOutcomeIsFalse : sameRuleRequiresSameOutcome ≡ false
    civilianIdentityIsOrganisationalResponsibility : Bool
    civilianIdentityIsOrganisationalResponsibilityIsFalse :
      civilianIdentityIsOrganisationalResponsibility ≡ false

canonicalMiddleEastObservationBoundary : MiddleEastObservationBoundary
canonicalMiddleEastObservationBoundary =
  middleEastObservationBoundary true refl false refl false refl
