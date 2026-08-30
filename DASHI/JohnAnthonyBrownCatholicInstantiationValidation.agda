module DASHI.JohnAnthonyBrownCatholicInstantiationValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.JohnAnthonyBrownCatholicInstantiationCoverageExact as Catholic

------------------------------------------------------------------------
-- Focused consumer root.
-- Suggested local command:
--   agda -i . DASHI/JohnAnthonyBrownCatholicInstantiationValidation.agda
------------------------------------------------------------------------

johnAnthonyBrownAttributionPinned :
  Catholic.BrownPaperReturn.author Catholic.currentCatholicInstantiationReturn
  ≡ "John Anthony Brown"
johnAnthonyBrownAttributionPinned = refl

partialCatholicCoverageInstalled :
  Catholic.CatholicInstantiationBoundary.partialCatholicCoordinateCoverageInstalled
    Catholic.canonicalCatholicInstantiationBoundary
  ≡ true
partialCatholicCoverageInstalled = refl

positiveReligiousDevelopmentEvidenceRetained :
  Catholic.CatholicInstantiationBoundary.positiveReligiousDevelopmentEvidenceRetained
    Catholic.canonicalCatholicInstantiationBoundary
  ≡ true
positiveReligiousDevelopmentEvidenceRetained = refl

punishmentFearInstalled :
  Catholic.CatholicCoverageFrontier.divinePunishmentFearInstalled
    Catholic.canonicalCatholicCoverageFrontier
  ≡ true
punishmentFearInstalled = refl

autonomySupportInstalled :
  Catholic.CatholicCoverageFrontier.parentAutonomySupportInstalled
    Catholic.canonicalCatholicCoverageFrontier
  ≡ true
autonomySupportInstalled = refl

familyTransmissionInstalled :
  Catholic.CatholicCoverageFrontier.familyTransmissionInstalled
    Catholic.canonicalCatholicCoverageFrontier
  ≡ true
familyTransmissionInstalled = refl

refusalPenaltyStillOpen :
  Catholic.CatholicCoverageFrontier.refusalPenaltyInstalled
    Catholic.canonicalCatholicCoverageFrontier
  ≡ false
refusalPenaltyStillOpen = refl

restrictedAlternativesStillOpen :
  Catholic.CatholicCoverageFrontier.restrictedAlternativesInstalled
    Catholic.canonicalCatholicCoverageFrontier
  ≡ false
restrictedAlternativesStillOpen = refl

adultClinicalOutcomeStillOpen :
  Catholic.CatholicCoverageFrontier.adultClinicalDistressPTSSInstalled
    Catholic.canonicalCatholicCoverageFrontier
  ≡ false
adultClinicalOutcomeStillOpen = refl

prospectiveCatholicEffectStillOpen :
  Catholic.CatholicCoverageFrontier.prospectiveCatholicChildhoodEffectInstalled
    Catholic.canonicalCatholicCoverageFrontier
  ≡ false
prospectiveCatholicEffectStillOpen = refl

catholicSampleNotChildhoodCausation :
  Catholic.CatholicSamplePromotesChildhoodCausalEffect -> ⊥
catholicSampleNotChildhoodCausation =
  Catholic.catholicSampleDoesNotPromoteChildhoodCausalEffect

fearOfPunishmentNotCoercion : Catholic.PunishmentFearPromotesCoercion -> ⊥
fearOfPunishmentNotCoercion = Catholic.punishmentFearDoesNotPromoteCoercion

bidirectionalCommunicationNotAutonomy :
  Catholic.BidirectionalCommunicationPromotesAutonomy -> ⊥
bidirectionalCommunicationNotAutonomy =
  Catholic.bidirectionalCommunicationDoesNotPromoteAutonomy

apostasyResearchNotConstrainedExit :
  Catholic.ApostasyResearchPromotesConstrainedExit -> ⊥
apostasyResearchNotConstrainedExit =
  Catholic.apostasyResearchDoesNotPromoteConstrainedExit

retrospectiveRecallNotProspectiveObservation :
  Catholic.RetrospectiveChildhoodRecallPromotesProspectiveRecord -> ⊥
retrospectiveRecallNotProspectiveObservation =
  Catholic.retrospectiveRecallDoesNotPromoteProspectiveRecord

mixedChristianSampleNotCatholicOnlyEffect :
  Catholic.CatholicAndProtestantSamplePromotesCatholicOnlyEffect -> ⊥
mixedChristianSampleNotCatholicOnlyEffect =
  Catholic.mixedChristianSampleDoesNotPromoteCatholicOnlyEffect

positiveTransmissionDoesNotRefuteCoercionQuestion :
  Catholic.PositiveTransmissionOutcomeRefutesCoercionMechanism -> ⊥
positiveTransmissionDoesNotRefuteCoercionQuestion =
  Catholic.positiveTransmissionOutcomeDoesNotRefuteCoercionMechanism

fullH1H5CatholicTargetStillOpen :
  Catholic.CatholicInstantiationBoundary.fullH1H5CatholicTargetClosed
    Catholic.canonicalCatholicInstantiationBoundary
  ≡ false
fullH1H5CatholicTargetStillOpen = refl
