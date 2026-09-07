module DASHI.Law.MaboHerzogMultiSourceProjectionCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.HerzogClassificationMultiSourceJoinExact as Join
import DASHI.Cognition.PNF.SensibLawMaboCrownRecognitionProjectionNonFactorabilityExact as Mabo
import DASHI.Cognition.PNF.SensibLawNativeTitleRecognitionDominationEverything as NativeTitle
import DASHI.Law.EvidenceProvenanceDependencyDagExact as Dag

------------------------------------------------------------------------
-- Shared formal lesson, distinct histories:
-- multiple administrative/legal surfaces can repeat one upstream proposition
-- without creating an independent underlying authority relation.
------------------------------------------------------------------------

data AdministrativeMultiplicityClaim : Set where
  repeatedRecognitionCreatesIndigenousAuthority
  repeatedThreatDocumentsCreateIndependentCorroboration
  repeatedClassificationCreatesIncidentCausation : AdministrativeMultiplicityClaim

data AdministrativeMultiplicityProducer : Set where
  indigenousAuthorityProducer
  independentThreatProducer
  incidentCausalProducer : AdministrativeMultiplicityProducer

reverseAdministrativeMultiplicity :
  AdministrativeMultiplicityClaim → AdministrativeMultiplicityProducer
reverseAdministrativeMultiplicity repeatedRecognitionCreatesIndigenousAuthority = indigenousAuthorityProducer
reverseAdministrativeMultiplicity repeatedThreatDocumentsCreateIndependentCorroboration = independentThreatProducer
reverseAdministrativeMultiplicity repeatedClassificationCreatesIncidentCausation = incidentCausalProducer

maboRecognitionDoesNotCreateAuthority :
  Mabo.crownRecognitionCreatesIndigenousOrder Mabo.canonicalCrownRecognitionObserverBoundary ≡ false
maboRecognitionDoesNotCreateAuthority = refl

maboRecognitionDoesNotExhaustCountry :
  Mabo.crownRecognitionExhaustsCountryRelation Mabo.canonicalCrownRecognitionObserverBoundary ≡ false
maboRecognitionDoesNotExhaustCountry = refl

nativeTitleSourceFirewallRetained :
  NativeTitle.sourceAttributionFirewallSurvivesPoliticalCritique
    NativeTitle.canonicalNativeTitleRecognitionDominationCapstone ≡ true
nativeTitleSourceFirewallRetained = refl

fourThreatDocumentsStillMayBeOneProducer :
  Join.atLeastTwoIndependentProducersClosed Join.canonicalFourCopiesOneProducer ≡ false
fourThreatDocumentsStillMayBeOneProducer = refl

multipleRecordsStillDoNotGuaranteeIndependence :
  Dag.multipleReceiptsAutomaticallyIndependent Dag.canonicalProvenanceDagBoundary ≡ false
multipleRecordsStillDoNotGuaranteeIndependence = refl

record MaboHerzogMultiplicityBoundary : Set where
  constructor maboHerzogMultiplicityBoundary
  field
    repeatedCrownRecognitionCreatesCountryAuthority : Bool
    repeatedCrownRecognitionCreatesCountryAuthorityIsFalse : repeatedCrownRecognitionCreatesCountryAuthority ≡ false
    repeatedSecurityDocumentsCreateIndependentThreatReality : Bool
    repeatedSecurityDocumentsCreateIndependentThreatRealityIsFalse : repeatedSecurityDocumentsCreateIndependentThreatReality ≡ false
    sharedMultiplicityFailureMakesHistoriesIdentical : Bool
    sharedMultiplicityFailureMakesHistoriesIdenticalIsFalse : sharedMultiplicityFailureMakesHistoriesIdentical ≡ false
    criticalInterpretationMayReplaceSourceProvenance : Bool
    criticalInterpretationMayReplaceSourceProvenanceIsFalse : criticalInterpretationMayReplaceSourceProvenance ≡ false
    administrativeMultiplicityMayIncreaseVisibilityWithoutIncreasingIndependence : Bool
    administrativeMultiplicityMayIncreaseVisibilityWithoutIncreasingIndependenceIsTrue : administrativeMultiplicityMayIncreaseVisibilityWithoutIncreasingIndependence ≡ true
    boundaryReference : String

open MaboHerzogMultiplicityBoundary public

canonicalMaboHerzogMultiplicityBoundary : MaboHerzogMultiplicityBoundary
canonicalMaboHerzogMultiplicityBoundary = maboHerzogMultiplicityBoundary
  false refl false refl false refl false refl true refl
  "shared formal provenance/compression lesson only: Mabo recognition and Herzog security documents retain distinct source traditions and legal histories"
