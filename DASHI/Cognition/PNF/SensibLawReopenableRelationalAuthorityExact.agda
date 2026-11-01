module DASHI.Cognition.PNF.SensibLawReopenableRelationalAuthorityExact where

------------------------------------------------------------------------
-- REOPENABLE / RELATIONAL AUTHORITY KERNEL
--
-- This is deliberately NOT a claim that there is one Indigenous, Aboriginal,
-- Torres Strait Islander, Native American, First Nations, or Haudenosaunee
-- decision procedure. Indigenous legal orders are plural and nation-specific.
--
-- Comparative motivation / recoverable sources:
--   * John Borrows, Canada's Indigenous Constitution (University of Toronto
--     Press, 2010), ISBN 9781442610381 -- Indigenous legal traditions as law,
--     plural legal sources and methods rather than a single pan-Indigenous code.
--   * Val Napoleon and Hadley Friedland, "An Inside Job: Engaging with
--     Indigenous Legal Traditions Through Stories", McGill Law Journal 61(4)
--     (2016) 725-754, DOI 10.7202/1038487ar -- explicit methodological work on
--     identifying legal principles, processes, responses and reasoning in
--     particular Indigenous legal traditions.
--
-- Extended deliberation, objection-triggered reopening, and consensus below
-- are DASHI decision-architecture primitives. A concrete nation-specific claim
-- must add its own source receipt before these primitives are instantiated as
-- empirical descriptions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge

------------------------------------------------------------------------
-- Decision procedure and closure rule are distinct.
------------------------------------------------------------------------

data DeliberationMode : Set where
  adversarialHearing : DeliberationMode
  majorityDecision : DeliberationMode
  extendedDeliberation : DeliberationMode
  consensusSeeking : DeliberationMode
  restorativeDeliberation : DeliberationMode
  nationSpecificProcedure : DeliberationMode


data ClosureRule : Set where
  authoritativeFinality : ClosureRule
  majorityClosure : ClosureRule
  objectionTriggersReopen : ClosureRule
  consensusClosure : ClosureRule
  legitimateResidualDisagreement : ClosureRule
  nationSpecificClosure : ClosureRule


record DecisionProcedure : Set where
  constructor decision-procedure
  field
    procedureId : String
    mode : DeliberationMode
    closure : ClosureRule
    affectedRelationsRepresented : Bool
    continuingObligationsRepresentable : Bool
    countryOrPlaceRelationRepresentable : Bool
    source : Edge.SourceIdentity
    empiricalInstantiation : Bool

open DecisionProcedure public

------------------------------------------------------------------------
-- Relational coordinates that a one-dimensional property/title observer may
-- collapse. These are representational capacities, not universal Indigenous
-- categories asserted of every legal order.
------------------------------------------------------------------------

data RelationalCoordinate : Set where
  custodianship : RelationalCoordinate
  permission : RelationalCoordinate
  ceremonialAuthority : RelationalCoordinate
  useObligation : RelationalCoordinate
  kinshipResponsibility : RelationalCoordinate
  careForCountryOrPlace : RelationalCoordinate
  repairCoordinate : RelationalCoordinate
  continuingRelationship : RelationalCoordinate
  intergenerationalObligation : RelationalCoordinate


record RelationalResolution : Set where
  constructor relational-resolution
  field
    participants : String
    relations : String
    obligations : String
    history : String
    placeOrCountry : String
    harm : String
    agreementOrResidualDisagreement : String
    repair : String
    continuingObligations : String

open RelationalResolution public

------------------------------------------------------------------------
-- Reopenability treats unresolved objection as information that may require
-- another pass rather than mechanically as a defeated minority position.
------------------------------------------------------------------------

data DeliberationState : Set where
  deliberationOpen : DeliberationState
  objectionRaised : DeliberationState
  reopened : DeliberationState
  consensusReached : DeliberationState
  residualDisagreementAccepted : DeliberationState
  authoritativelyClosed : DeliberationState


reopenOnObjection : DeliberationState → DeliberationState
reopenOnObjection deliberationOpen = deliberationOpen
reopenOnObjection objectionRaised = reopened
reopenOnObjection reopened = reopened
reopenOnObjection consensusReached = consensusReached
reopenOnObjection residualDisagreementAccepted = residualDisagreementAccepted
reopenOnObjection authoritativelyClosed = authoritativelyClosed

objectionReopens : reopenOnObjection objectionRaised ≡ reopened
objectionReopens = refl

------------------------------------------------------------------------
-- Non-collapse laws.
------------------------------------------------------------------------

data DecisionQualityEqualsDecisionSpeed : Set where
data UnresolvedDissentMeansIrrationalObstruction : Set where
data ConflictResolutionRequiresWinnerLoser : Set where
data LegalAuthorityRequiresCentralisedJudge : Set where
data RemedyRequiresDamagesOrInjunction : Set where
data StatePropertyTitleExhaustsRelationalLaw : Set where
data GenericRelationalModelIsUniversalIndigenousPractice : Set where
data NoCommonLawDutyMeansNoRelationalObligation : Set where

decisionQualityDoesNotEqualSpeedByDefinition : DecisionQualityEqualsDecisionSpeed → ⊥
decisionQualityDoesNotEqualSpeedByDefinition ()

dissentIsNotEncodedAsIrrationalByDefinition : UnresolvedDissentMeansIrrationalObstruction → ⊥
dissentIsNotEncodedAsIrrationalByDefinition ()

conflictResolutionNeedNotBeWinnerLoserByDefinition : ConflictResolutionRequiresWinnerLoser → ⊥
conflictResolutionNeedNotBeWinnerLoserByDefinition ()

authorityNeedNotBeCentralJudgeByDefinition : LegalAuthorityRequiresCentralisedJudge → ⊥
authorityNeedNotBeCentralJudgeByDefinition ()

remedyNeedNotBeDamagesOrInjunctionByDefinition : RemedyRequiresDamagesOrInjunction → ⊥
remedyNeedNotBeDamagesOrInjunctionByDefinition ()

propertyTitleDoesNotExhaustRelationalCoordinates : StatePropertyTitleExhaustsRelationalLaw → ⊥
propertyTitleDoesNotExhaustRelationalCoordinates ()

genericModelDoesNotBecomePanIndigenousClaim :
  GenericRelationalModelIsUniversalIndigenousPractice → ⊥
genericModelDoesNotBecomePanIndigenousClaim ()

noCommonLawDutyDoesNotEraseOtherObligationSystems :
  NoCommonLawDutyMeansNoRelationalObligation → ⊥
noCommonLawDutyDoesNotEraseOtherObligationSystems ()

------------------------------------------------------------------------
-- A concrete empirical instantiation must name the people/legal order and a
-- recoverable source. No nation-specific fixture is fabricated here.
------------------------------------------------------------------------

record NationSpecificDeliberationReceipt : Set where
  constructor nation-specific-deliberation-receipt
  field
    peopleOrLegalOrder : String
    describedProcedure : String
    describedClosureRule : String
    authorOrInstitution : String
    sourceTitle : String
    stableIdentifier : String
    directSourceSupport : Bool
    generalizedToAllIndigenousPeoples : Bool
    generalizedToAllIndigenousPeoplesIsFalse :
      generalizedToAllIndigenousPeoples ≡ false

open NationSpecificDeliberationReceipt public
