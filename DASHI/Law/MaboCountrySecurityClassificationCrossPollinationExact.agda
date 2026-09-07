module DASHI.Law.MaboCountrySecurityClassificationCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawMaboCrownRecognitionProjectionNonFactorabilityExact as Mabo
import DASHI.Cognition.PNF.SensibLawNativeTitleRecognitionDominationEverything as NativeTitle
import DASHI.Law.SecurityClassificationInputLineageDagExact as Lineage
import DASHI.Law.SecurityClassificationProvenanceBidiExact as Security

------------------------------------------------------------------------
-- Mabo/Country x security-classification compression.
-- Crown/native-title recognition and police/security classification are not the
-- same historical doctrine.  They share a formal projection problem: a locally
-- useful administrative surface may erase relations needed by another consumer.
------------------------------------------------------------------------

data PoliticalAssemblySituatedState : Set where
  sameSecurityLabelCountryAuthorityPresent
  sameSecurityLabelCountryAuthorityErased
  : PoliticalAssemblySituatedState

data SecurityAdministrativeSurface : Set where
  samePublicOrderClassification : SecurityAdministrativeSurface

data PoliticalAuthorityOutcome : Set where
  countryAuthorityRetained
  countryAuthorityInvisible : PoliticalAuthorityOutcome

securityObserver : PoliticalAssemblySituatedState → SecurityAdministrativeSurface
securityObserver sameSecurityLabelCountryAuthorityPresent = samePublicOrderClassification
securityObserver sameSecurityLabelCountryAuthorityErased = samePublicOrderClassification

politicalAuthorityOutcome : PoliticalAssemblySituatedState → PoliticalAuthorityOutcome
politicalAuthorityOutcome sameSecurityLabelCountryAuthorityPresent = countryAuthorityRetained
politicalAuthorityOutcome sameSecurityLabelCountryAuthorityErased = countryAuthorityInvisible

politicalAuthorityOutcomesDiffer :
  politicalAuthorityOutcome sameSecurityLabelCountryAuthorityPresent ≡
  politicalAuthorityOutcome sameSecurityLabelCountryAuthorityErased → ⊥
politicalAuthorityOutcomesDiffer ()

securityClassificationCannotRecoverAuthorityWitness :
  INF.NonFactorabilityWitness securityObserver politicalAuthorityOutcome
securityClassificationCannotRecoverAuthorityWitness = INF.nonFactorabilityWitness
  sameSecurityLabelCountryAuthorityPresent
  sameSecurityLabelCountryAuthorityErased
  refl
  politicalAuthorityOutcomesDiffer

securityClassificationCannotFactorAuthority :
  INF.FactorsThrough securityObserver politicalAuthorityOutcome → ⊥
securityClassificationCannotFactorAuthority =
  INF.witnessRulesOutEveryFlatFactorisation securityClassificationCannotRecoverAuthorityWitness

securityDominantChartReceipt :
  Compression.ProjectionInadequacyReceipt securityObserver politicalAuthorityOutcome
securityDominantChartReceipt = Compression.projection-inadequacy-receipt
  Compression.administrativeClassificationCompression
  "police/security public-order classification observer"
  "consumer requiring Country, sovereign-authority and political-meaning coordinates"
  "same security label can hide whether antecedent Country/community authority is represented or erased"
  securityClassificationCannotRecoverAuthorityWitness
  true refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Explicit donor retention from Mabo/native-title capstone.
------------------------------------------------------------------------

maboRecognitionStillCannotRecoverAuthority :
  INF.FactorsThrough Mabo.crownRecognitionObserver Mabo.indigenousAuthorityOutcome → ⊥
maboRecognitionStillCannotRecoverAuthority = Mabo.crownRecognitionDoesNotFactorIndigenousAuthority

nativeTitleMajorLegalAdvanceRetained :
  NativeTitle.legalAdvanceVisible NativeTitle.canonicalNativeTitleRecognitionDominationCapstone ≡ true
nativeTitleMajorLegalAdvanceRetained = refl

nativeTitleStillDoesNotResolveCession :
  NativeTitle.sovereigntyCessionResolvedByNativeTitleDoctrine NativeTitle.canonicalNativeTitleRecognitionDominationCapstone ≡ false
nativeTitleStillDoesNotResolveCession = refl

sourceFirewallRetained :
  NativeTitle.sourceAttributionFirewallSurvivesPoliticalCritique NativeTitle.canonicalNativeTitleRecognitionDominationCapstone ≡ true
sourceFirewallRetained = refl

------------------------------------------------------------------------
-- Country/self-determination residuals for security consumers.
------------------------------------------------------------------------

data SecurityCountryClaim : Set where
  publicOrderLabelExhaustsPoliticalMeaning
  securityClassificationExhaustsCountryAuthority
  securityClassificationExhaustsSovereigntyClaim
  securityClassificationExhaustsSelfDeterminationClaim
  countryOrSovereigntyContentAffectedRiskClassification : SecurityCountryClaim

data SecurityCountryProducer : Set where
  completePoliticalMeaningProducer
  countryAuthorityResidualProducer
  sovereigntyResidualProducer
  selfDeterminationResidualProducer
  classificationInputContentProducer : SecurityCountryProducer

reverseSecurityCountry : SecurityCountryClaim → SecurityCountryProducer
reverseSecurityCountry publicOrderLabelExhaustsPoliticalMeaning = completePoliticalMeaningProducer
reverseSecurityCountry securityClassificationExhaustsCountryAuthority = countryAuthorityResidualProducer
reverseSecurityCountry securityClassificationExhaustsSovereigntyClaim = sovereigntyResidualProducer
reverseSecurityCountry securityClassificationExhaustsSelfDeterminationClaim = selfDeterminationResidualProducer
reverseSecurityCountry countryOrSovereigntyContentAffectedRiskClassification = classificationInputContentProducer

record SecurityCountryBoundary : Set where
  constructor securityCountryBoundary
  field
    legalSecurityClassificationCreatesUnderlyingAuthority : Bool
    legalSecurityClassificationCreatesUnderlyingAuthorityIsFalse : legalSecurityClassificationCreatesUnderlyingAuthority ≡ false
    administrativeRecognitionExhaustsCountry : Bool
    administrativeRecognitionExhaustsCountryIsFalse : administrativeRecognitionExhaustsCountry ≡ false
    publicOrderClassificationExhaustsPoliticalMeaning : Bool
    publicOrderClassificationExhaustsPoliticalMeaningIsFalse : publicOrderClassificationExhaustsPoliticalMeaning ≡ false
    sharedCompressionPatternMakesMaboAndHerzogSameDoctrine : Bool
    sharedCompressionPatternMakesMaboAndHerzogSameDoctrineIsFalse : sharedCompressionPatternMakesMaboAndHerzogSameDoctrine ≡ false
    criticalColonialityLensAutomaticallyProvesPoliceIntent : Bool
    criticalColonialityLensAutomaticallyProvesPoliceIntentIsFalse : criticalColonialityLensAutomaticallyProvesPoliceIntent ≡ false

canonicalSecurityCountryBoundary : SecurityCountryBoundary
canonicalSecurityCountryBoundary = securityCountryBoundary false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- Lineage bridge: if Country/self-determination content is alleged to have
-- affected a risk classification, the required producer is the actual input
-- atom and its lineage, not the critical interpretation alone.
------------------------------------------------------------------------

countryClassificationLineageProducer : Lineage.LineageProducer
countryClassificationLineageProducer = Lineage.classificationContentAndCarrierProducer

classificationInputForeignProducer : Security.SecurityClassificationProducer
classificationInputForeignProducer = Security.foreignLiaisonProducer

record ColonialClassificationAudit : Set where
  constructor colonialClassificationAudit
  field
    dominantChartReceiptOwned : Bool
    dominantChartReceiptOwnedIsTrue : dominantChartReceiptOwned ≡ true
    countryResidualRequired : Bool
    countryResidualRequiredIsTrue : countryResidualRequired ≡ true
    actualClassificationInputAcquired : Bool
    actualClassificationInputAcquiredIsFalse : actualClassificationInputAcquired ≡ false
    colonialityInterpretationCreatesHistoricalFact : Bool
    colonialityInterpretationCreatesHistoricalFactIsFalse : colonialityInterpretationCreatesHistoricalFact ≡ false
    auditReference : String

open ColonialClassificationAudit public

canonicalColonialClassificationAudit : ColonialClassificationAudit
canonicalColonialClassificationAudit = colonialClassificationAudit
  true refl true refl false refl false refl
  "Mabo/Country compression identifies the missing consumer coordinates; Herzog-specific lineage evidence is still required to prove those coordinates affected police classification"
