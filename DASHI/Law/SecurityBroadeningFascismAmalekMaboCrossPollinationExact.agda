module DASHI.Law.SecurityBroadeningFascismAmalekMaboCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Law.SecurityThreatSemanticBroadeningTopologyExact as Broadening
import DASHI.Law.FascismAtrocitySourceCrossPollinationExact as Fascism
import DASHI.Law.HerzogFascismAntifascistAmalekCrossPollinationExact as Cross
import DASHI.Law.MaboCountrySecurityClassificationCrossPollinationExact as Mabo

------------------------------------------------------------------------
-- Cross-pollination boundary.
-- Semantic broadening may instantiate the same formal mechanism audited as
-- collective-guilt transport / distinction erasure, but a source-bounded
-- broadening receipt remains distinct from a full fascism diagnosis.
------------------------------------------------------------------------

data BroadeningMechanism : Set where
  individualToGroupAttribution
  groupToWholeAssemblyAttribution
  politicalMeaningErasure
  enemyRolePropagation
  terminalisingPropagation
  correctionPreservingInterruption : BroadeningMechanism

broadeningToFascismFeature : BroadeningMechanism → Fascism.FascismFeature
broadeningToFascismFeature individualToGroupAttribution = Fascism.collectiveGuiltTransport
broadeningToFascismFeature groupToWholeAssemblyAttribution = Fascism.collectiveGuiltTransport
broadeningToFascismFeature politicalMeaningErasure = Fascism.distinctionErasure
broadeningToFascismFeature enemyRolePropagation = Fascism.provenanceWeaponisation
broadeningToFascismFeature terminalisingPropagation = Fascism.terminalisation
broadeningToFascismFeature correctionPreservingInterruption = Fascism.distinctionErasure

------------------------------------------------------------------------
-- Amalek promotion-chain adapter.
------------------------------------------------------------------------

amalekCollectivePropagationCoordinate : Cross.AmalekAuditCoordinate
amalekCollectivePropagationCoordinate = Cross.collectivePropagation

amalekTerminalisationCoordinate : Cross.AmalekAuditCoordinate
amalekTerminalisationCoordinate = Cross.terminalisationEvidence

record AmalekBroadeningBoundary : Set where
  constructor amalekBroadeningBoundary
  field
    modernRoleBindingProvesCollectivePropagation : Bool
    modernRoleBindingProvesCollectivePropagationIsFalse : modernRoleBindingProvesCollectivePropagation ≡ false
    collectivePropagationProvesOperationalCommand : Bool
    collectivePropagationProvesOperationalCommandIsFalse : collectivePropagationProvesOperationalCommand ≡ false
    broadeningIntoEnemyCategoryProvesTerminalisation : Bool
    broadeningIntoEnemyCategoryProvesTerminalisationIsFalse : broadeningIntoEnemyCategoryProvesTerminalisation ≡ false

canonicalAmalekBroadeningBoundary : AmalekBroadeningBoundary
canonicalAmalekBroadeningBoundary = amalekBroadeningBoundary false refl false refl false refl

------------------------------------------------------------------------
-- Mabo/Country adapter.
-- Broadening can erase political/Country authority in the same way a dominant
-- administrative chart can erase an independently modelled relation.  Shared
-- formal shape does not equate histories.
------------------------------------------------------------------------

countryResidualProducer : Mabo.SecurityCountryProducer
countryResidualProducer = Mabo.countryAuthorityResidualProducer

selfDeterminationResidualProducer : Mabo.SecurityCountryProducer
selfDeterminationResidualProducer = Mabo.selfDeterminationResidualProducer

record MaboBroadeningBoundary : Set where
  constructor maboBroadeningBoundary
  field
    broaderCrowdLabelExhaustsCountryAuthority : Bool
    broaderCrowdLabelExhaustsCountryAuthorityIsFalse : broaderCrowdLabelExhaustsCountryAuthority ≡ false
    broaderCrowdLabelExhaustsPoliticalMeaning : Bool
    broaderCrowdLabelExhaustsPoliticalMeaningIsFalse : broaderCrowdLabelExhaustsPoliticalMeaning ≡ false
    sharedErasureMakesHistoricalDoctrinesIdentical : Bool
    sharedErasureMakesHistoricalDoctrinesIdenticalIsFalse : sharedErasureMakesHistoricalDoctrinesIdentical ≡ false

canonicalMaboBroadeningBoundary : MaboBroadeningBoundary
canonicalMaboBroadeningBoundary = maboBroadeningBoundary false refl false refl false refl

------------------------------------------------------------------------
-- Antifascist repair is a transformation constraint, not a rival population
-- label: restore distinctions, reopen correction, and block unjustified scope
-- expansion.
------------------------------------------------------------------------

data BroadeningRepairClaim : Set where
  restoreIndividualGroupDistinction
  requireEvidenceForScopeExpansion
  reopenCorrectionAfterClassification
  preserveCountryPoliticalMeaning : BroadeningRepairClaim

data BroadeningRepairProducer : Set where
  distinctionRepairProducer
  scopeEvidenceProducer
  correctionChannelProducer
  residualCoordinateProducer : BroadeningRepairProducer

reverseRepair : BroadeningRepairClaim → BroadeningRepairProducer
reverseRepair restoreIndividualGroupDistinction = distinctionRepairProducer
reverseRepair requireEvidenceForScopeExpansion = scopeEvidenceProducer
reverseRepair reopenCorrectionAfterClassification = correctionChannelProducer
reverseRepair preserveCountryPoliticalMeaning = residualCoordinateProducer

record CrossPollinationBoundary : Set where
  constructor crossPollinationBoundary
  field
    individualToCollectiveBroadeningAutomaticallyIsFascism : Bool
    individualToCollectiveBroadeningAutomaticallyIsFascismIsFalse : individualToCollectiveBroadeningAutomaticallyIsFascism ≡ false
    broadeningMayFeedCollectiveGuiltAudit : Bool
    broadeningMayFeedCollectiveGuiltAuditIsTrue : broadeningMayFeedCollectiveGuiltAudit ≡ true
    countryCriticalLensSuppliesMissingThreatEvidence : Bool
    countryCriticalLensSuppliesMissingThreatEvidenceIsFalse : countryCriticalLensSuppliesMissingThreatEvidence ≡ false
    antifascistRepairRequiresCollectiveCounterPunishment : Bool
    antifascistRepairRequiresCollectiveCounterPunishmentIsFalse : antifascistRepairRequiresCollectiveCounterPunishment ≡ false

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary = crossPollinationBoundary false refl true refl false refl false refl
