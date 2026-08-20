module DASHI.Governance.DependentReligiousEntrapmentCandidateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DependentAuthorityCoercionKernel as Coercion
import DASHI.Governance.ChildReligiousCoercionResearchBridge as Research

------------------------------------------------------------------------
-- SOURCE CALIBRATION
--
-- Mary Landenburger,
-- "A process of entrapment in and recovery from an abusive relationship",
-- Issues in Mental Health Nursing 10(3-4):209-227 (1989).
-- DOI: 10.3109/01612848909140846.
--
-- Evan Stark,
-- "Coercive Control: The Entrapment of Women in Personal Life",
-- Oxford University Press (2007).
-- DOI: 10.1093/oso/9780195154276.001.0001.
--
-- United Nations,
-- "Convention on the Rights of the Child" (1989), especially Articles
-- 5, 12 and 14. Treaty source; no DOI asserted here.
--
-- Landenburger and Stark establish an entrapment/coercive-control construct
-- in abusive intimate relationships. They do NOT establish that ordinary
-- religious upbringing, Catholic formation, or childhood belief transmission
-- instantiates that construct. The exact candidate below is DASHI's bounded
-- mechanism carrier and requires domain-specific witnesses.
------------------------------------------------------------------------

record EntrapmentSourceRole : Set where
  constructor entrapmentSourceRole
  field
    authors : String
    title : String
    identifier : String
    boundedRole : String

landenburgerSource : EntrapmentSourceRole
landenburgerSource =
  entrapmentSourceRole
    "Mary Landenburger"
    "A process of entrapment in and recovery from an abusive relationship"
    "DOI 10.3109/01612848909140846"
    "construct/mechanism source for relational entrapment; population is abusive intimate relationships, not religious childhood"

starkSource : EntrapmentSourceRole
starkSource =
  entrapmentSourceRole
    "Evan Stark"
    "Coercive Control: The Entrapment of Women in Personal Life"
    "DOI 10.1093/oso/9780195154276.001.0001"
    "construct/mechanism source for coercive control and entrapment; does not instantiate Catholic-childhood exposure"

crcSource : EntrapmentSourceRole
crcSource =
  entrapmentSourceRole
    "United Nations General Assembly"
    "Convention on the Rights of the Child"
    "1989; Articles 5, 12, 14"
    "rights vocabulary for evolving capacities, participation, and freedom of thought/conscience/religion; not an age-18 ban on religious formation"

------------------------------------------------------------------------
-- The candidate is not defined by religion. It is a conjunction of
-- dependence, low exit capacity and several mechanism witnesses.
------------------------------------------------------------------------

record DependentReligiousEntrapmentCandidate : Set where
  constructor dependentReligiousEntrapmentCandidate
  field
    developmentalState : Coercion.DevelopmentalState
    authorityRelation : Coercion.AuthorityRelation
    transmission : Coercion.TransmissionEvent

    materiallyDependent : Set
    materiallyDependentWitness : materiallyDependent

    lowPracticalExitCapacity : Set
    lowPracticalExitCapacityWitness : lowPracticalExitCapacity

    divineSanctionPresent : Set
    divineSanctionWitness : divineSanctionPresent

    familialBelongingPenaltyPresent : Set
    familialBelongingPenaltyWitness : familialBelongingPenaltyPresent

    counterEvidenceRestricted : Coercion.counterEvidenceRestricted transmission ≡ true
    doubtPenalised : Coercion.doubtPenalised transmission ≡ true
    authorityClosed : Coercion.authorityClosed transmission ≡ true
    exitConstrained : Coercion.exitConstrained transmission ≡ true

open DependentReligiousEntrapmentCandidate public

------------------------------------------------------------------------
-- A bare transmission event cannot manufacture this candidate. The missing
-- dependency and mechanism witnesses remain visible in the type.
------------------------------------------------------------------------

data ReligiousTransmissionAloneEstablishesEntrapment : Set where

data StrongDoctrineAloneEstablishesEntrapment : Set where

data ChildhoodExposureAloneEstablishesEntrapment : Set where

religiousTransmissionAloneDoesNotEstablishEntrapment :
  ReligiousTransmissionAloneEstablishesEntrapment → ⊥
religiousTransmissionAloneDoesNotEstablishEntrapment ()

strongDoctrineAloneDoesNotEstablishEntrapment :
  StrongDoctrineAloneEstablishesEntrapment → ⊥
strongDoctrineAloneDoesNotEstablishEntrapment ()

childhoodExposureAloneDoesNotEstablishEntrapment :
  ChildhoodExposureAloneEstablishesEntrapment → ⊥
childhoodExposureAloneDoesNotEstablishEntrapment ()

------------------------------------------------------------------------
-- Cross-pollination with the existing research bridge.
-- The dimensions the paper actually proposes -- fear, punishment,
-- epistemic closure, disclosure suppression and exit restriction -- are
-- already represented independently from the label "religion".
------------------------------------------------------------------------

record EntrapmentResearchCoordinates : Set where
  constructor entrapmentResearchCoordinates
  field
    exposureDimensions : List Research.ExposureDimension
    requiresFrequencySeverityDuration : Bool
    requiresDevelopmentalStage : Bool
    requiresExitRestriction : Bool
    requiresRefusalPenalty : Bool

canonicalEntrapmentResearchCoordinates : EntrapmentResearchCoordinates
canonicalEntrapmentResearchCoordinates =
  entrapmentResearchCoordinates
    (Research.fearExposure
      ∷ Research.compulsionExposure
      ∷ Research.punishmentExposure
      ∷ Research.isolationExposure
      ∷ Research.epistemicClosureExposure
      ∷ Research.disclosureSuppressionExposure
      ∷ [])
    true true true true

record DependentReligiousEntrapmentBoundary : Set where
  constructor dependentReligiousEntrapmentBoundary
  field
    entrapmentConstructExists : Bool
    constructSourceInstantiatesCatholicChildhood : Bool
    ordinaryReligiousTeachingEqualsEntrapment : Bool
    familyBelongingPenaltyCanBeRelevantMechanism : Bool
    divinePunishmentCanBeRelevantMechanism : Bool
    legalFalseImprisonmentAutomaticallyFollows : Bool
    legalSlaveryAutomaticallyFollows : Bool

canonicalDependentReligiousEntrapmentBoundary :
  DependentReligiousEntrapmentBoundary
canonicalDependentReligiousEntrapmentBoundary =
  dependentReligiousEntrapmentBoundary
    true false false true true false false
