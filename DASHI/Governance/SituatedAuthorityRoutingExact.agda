module DASHI.Governance.SituatedAuthorityRoutingExact where

------------------------------------------------------------------------
-- SITUATED AUTHORITY ROUTING
--
-- Justice-relevant response is represented as proof-carrying routing rather
-- than an intrinsic ranking of institutional labels.  A route is admissible
-- only when the application supplies distinct witnesses for sufficiency,
-- competence, mandate, current authority, subject legibility, safety,
-- reviewability, and repair capacity.
--
-- Source / cross-pollination calibration:
--
-- Kimberle Williams Crenshaw,
-- "Mapping the Margins: Intersectionality, Identity Politics, and Violence
-- against Women of Color", Stanford Law Review 43(6), 1241-1299 (1991).
-- DOI: 10.2307/1229039.
-- Used through DASHI's situated/non-factorability discipline; the routing
-- calculus is a DASHI construction, not a theorem attributed to Crenshaw.
--
-- Hanna Fenichel Pitkin, The Concept of Representation (1967).
-- Book; no DOI assigned.  Used through the existing scoped/recallable mandate
-- grammar.  Role possession alone is not promoted to legitimate authority.
--
-- Alice Brown, Jill Lawrence, Marita Basson, Megan Axelsen, Petrea Redmond,
-- Joanna Turner, Suzanne Maloney, Linda Galligan,
-- "The creation of a nudging protocol to support online student engagement in
-- higher education", Active Learning in Higher Education 24(3), 257-271.
-- DOI: 10.1177/14697874211039077.
-- Cross-pollenated only for the signal -> reviewed candidate -> intervention
-- boundary; pedagogical routing does not establish political authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DiachronicDelegatedAuthorityBoundary as Diachronic
import DASHI.Reasoning.RelationalChronologyProjectionBoundary as Chronology
import DASHI.Reasoning.RelationalSharedStateUpdate as Shared

------------------------------------------------------------------------
-- Generic proof-carrying router.
------------------------------------------------------------------------

record RoutingSystem (Situation Route : Set) : Set₁ where
  field
    Sufficient : Situation → Route → Set
    Competent : Situation → Route → Set
    Mandated : Situation → Route → Set
    CurrentAuthority : Situation → Route → Set
    SubjectLegible : Situation → Route → Set
    Safe : Situation → Route → Set
    Reviewable : Situation → Route → Set
    RepairCapable : Situation → Route → Set
    dominationCost : Situation → Route → Nat

open RoutingSystem public

record AdmissibleRoute
    {Situation Route : Set}
    (system : RoutingSystem Situation Route)
    (situation : Situation)
    (route : Route) : Set₁ where
  constructor admissibleRoute
  field
    sufficient : Sufficient system situation route
    competent : Competent system situation route
    mandated : Mandated system situation route
    currentAuthority : CurrentAuthority system situation route
    subjectLegible : SubjectLegible system situation route
    safe : Safe system situation route
    reviewable : Reviewable system situation route
    repairCapable : RepairCapable system situation route

open AdmissibleRoute public

NoMoreDomineering :
  ∀ {Situation Route}
    (system : RoutingSystem Situation Route) →
    Situation → Route → Route → Set
NoMoreDomineering system situation left right =
  dominationCost system situation left ≤ dominationCost system situation right

StrictlyLessDomineering :
  ∀ {Situation Route}
    (system : RoutingSystem Situation Route) →
    Situation → Route → Route → Set
StrictlyLessDomineering system situation left right =
  suc (dominationCost system situation left) ≤
  dominationCost system situation right

record PreferredRoute
    {Situation Route : Set}
    (system : RoutingSystem Situation Route)
    (situation : Situation)
    (route : Route) : Set₁ where
  constructor preferredRoute
  field
    admissible : AdmissibleRoute system situation route
    minimalAmongAdmissible :
      (other : Route) →
      AdmissibleRoute system situation other →
      NoMoreDomineering system situation route other

open PreferredRoute public

-- This is the formal "sufficiency first, then least domination" carrier.
routeToLeastDomineeringSufficientSituatedAuthority :
  ∀ {Situation Route}
    {system : RoutingSystem Situation Route}
    {situation : Situation}
    {route : Route} →
  PreferredRoute system situation route →
  AdmissibleRoute system situation route
routeToLeastDomineeringSufficientSituatedAuthority = PreferredRoute.admissible

------------------------------------------------------------------------
-- Responder-family extension and the residual police domain.
--
-- A richer family adds possible responders without deleting the old ones.
-- If police was already present in the base family, then adding alternatives
-- cannot create a new state in which police has no less-domineering admissible
-- alternative.  This is the exact monotonic form of the reallocation claim.
------------------------------------------------------------------------

ResponderFamily : Set → Set₁
ResponderFamily Route = Route → Set

record FamilyExtension
    {Route : Set}
    (base richer : ResponderFamily Route) : Set₁ where
  constructor familyExtension
  field
    included : (route : Route) → base route → richer route

open FamilyExtension public

record ResidualPoliceDomain
    {Situation Route : Set}
    (system : RoutingSystem Situation Route)
    (police : Route)
    (family : ResponderFamily Route)
    (situation : Situation) : Set₁ where
  constructor residualPoliceDomain
  field
    policeAvailable : family police
    policeAdmissible : AdmissibleRoute system situation police
    noLessDomineeringAlternative :
      (other : Route) →
      family other →
      AdmissibleRoute system situation other →
      StrictlyLessDomineering system situation other police →
      ⊥

open ResidualPoliceDomain public

richerResponderFamilyCannotExpandResidualPoliceDomain :
  ∀ {Situation Route}
    {system : RoutingSystem Situation Route}
    {police : Route}
    {base richer : ResponderFamily Route}
    {situation : Situation} →
  FamilyExtension base richer →
  base police →
  ResidualPoliceDomain system police richer situation →
  ResidualPoliceDomain system police base situation
richerResponderFamilyCannotExpandResidualPoliceDomain
  extension policeInBase residual =
  residualPoliceDomain
    policeInBase
    (policeAdmissible residual)
    λ other otherInBase otherAdmissible less →
      noLessDomineeringAlternative residual
        other
        (included extension other otherInBase)
        otherAdmissible
        less

policeRouteRequiresResidualNecessity :
  ∀ {Situation Route}
    {system : RoutingSystem Situation Route}
    {police : Route}
    {family : ResponderFamily Route}
    {situation : Situation} →
  ResidualPoliceDomain system police family situation →
  (other : Route) →
  family other →
  AdmissibleRoute system situation other →
  StrictlyLessDomineering system situation other police →
  ⊥
policeRouteRequiresResidualNecessity =
  ResidualPoliceDomain.noLessDomineeringAlternative

------------------------------------------------------------------------
-- Concrete routing countermodel.
-- Some situations can genuinely route to a coercive/public-authority response
-- while that fact does not make the same route the default for another
-- situated state.
------------------------------------------------------------------------

data DemoSituation : Set where
  nonviolentDistress imminentViolentThreat : DemoSituation

data DemoRoute : Set where
  peerRoute clinicianRoute elderCommunityRoute policeRoute : DemoRoute

demoSelectedRoute : DemoSituation → DemoRoute
demoSelectedRoute nonviolentDistress = clinicianRoute
demoSelectedRoute imminentViolentThreat = policeRoute

policeNecessaryInOneDemoSituation :
  demoSelectedRoute imminentViolentThreat ≡ policeRoute
policeNecessaryInOneDemoSituation = refl

somePoliceNecessityDoesNotEstablishPoliceDefault :
  ((situation : DemoSituation) → demoSelectedRoute situation ≡ policeRoute) →
  ⊥
somePoliceNecessityDoesNotEstablishPoliceDefault allegedDefault with
  allegedDefault nonviolentDistress
... | ()

------------------------------------------------------------------------
-- Protective/supportive role cannot self-authorise an override.
--
-- The generic router exposes this as an independent CurrentAuthority
-- obligation.  The finite countermodel below gives a protective-looking route
-- all other obligations while making current authority empty.
------------------------------------------------------------------------

data ProtectiveSituation : Set where
  supportedDecisionSituation : ProtectiveSituation

data ProtectiveRoute : Set where
  formerSupporterRoute : ProtectiveRoute

data NoCurrentAuthority : Set where

protectiveRoutingSystem :
  RoutingSystem ProtectiveSituation ProtectiveRoute
protectiveRoutingSystem = record
  { Sufficient = λ _ _ → ⊤
  ; Competent = λ _ _ → ⊤
  ; Mandated = λ _ _ → ⊤
  ; CurrentAuthority = λ _ _ → NoCurrentAuthority
  ; SubjectLegible = λ _ _ → ⊤
  ; Safe = λ _ _ → ⊤
  ; Reviewable = λ _ _ → ⊤
  ; RepairCapable = λ _ _ → ⊤
  ; dominationCost = λ _ _ → 1
  }

ProtectiveRoleDoesNotSelfAuthoriseIntervention :
  AdmissibleRoute
    protectiveRoutingSystem
    supportedDecisionSituation
    formerSupporterRoute →
  ⊥
ProtectiveRoleDoesNotSelfAuthoriseIntervention admissible with
  currentAuthority admissible
... | ()

supportRoleDoesNotAuthoriseOverride :
  Diachronic.supporterCannotSelfAuthoriseOverride
    Diachronic.canonicalSupportedDecisionConditions
  ≡ true
supportRoleDoesNotAuthoriseOverride = refl

revokedProtectiveAuthorityCannotSelfRestoreFromPastEvidence :
  Diachronic.historicalEvidenceRestoresAuthority
    Diachronic.canonicalDiachronicAuthorityPromotionBoundary
  ≡ false
revokedProtectiveAuthorityCannotSelfRestoreFromPastEvidence =
  Diachronic.canonicalHistoricalEvidenceRestoresAuthorityFalse

------------------------------------------------------------------------
-- Community governance requires decision sensitivity, not merely consultation.
-- The existing canonical pseudo-consultation episode requested input but the
-- decision was insensitive to it.  It therefore cannot inhabit this witness.
------------------------------------------------------------------------

record CommunityAuthorityWitness
    (episode : Shared.ConsultationEpisode) : Set where
  constructor communityAuthorityWitness
  field
    voiceHeard : Set
    uptakeAvailable : Set
    decisionSensitive :
      Shared.decisionSensitiveToInput episode ≡ true
    scopeWitness : Set
    revocabilityWitness : Set
    safeguardingWitness : Set

open CommunityAuthorityWitness public

consultationDoesNotEstablishCommunityGovernance :
  CommunityAuthorityWitness Chronology.canonicalConsultationEpisode →
  ⊥
consultationDoesNotEstablishCommunityGovernance witness with
  decisionSensitive witness
... | ()

hearingDoesNotEstablishDecisionSensitivity :
  Shared.decisionSensitiveToInput Chronology.canonicalConsultationEpisode
  ≡ false
hearingDoesNotEstablishDecisionSensitivity = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SituatedAuthorityRoutingBoundary : Set where
  constructor situatedAuthorityRoutingBoundary
  field
    policeNecessarySomewhereImpliesPoliceDefault : Bool
    protectiveRoleSelfAuthorisesOverride : Bool
    consultationAloneCreatesCommunityAuthority : Bool
    richerResponderFamilyMayCreateNewResidualPoliceNeed : Bool
    routeAdmissibilityRequiresCurrentAuthority : Bool
    routeAdmissibilityRequiresSafety : Bool
    routeAdmissibilityRequiresRepairCapacity : Bool

canonicalSituatedAuthorityRoutingBoundary : SituatedAuthorityRoutingBoundary
canonicalSituatedAuthorityRoutingBoundary =
  situatedAuthorityRoutingBoundary
    false false false false true true true
