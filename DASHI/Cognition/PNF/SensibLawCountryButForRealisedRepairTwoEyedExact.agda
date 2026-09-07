module DASHI.Cognition.PNF.SensibLawCountryButForRealisedRepairTwoEyedExact where

------------------------------------------------------------------------
-- COUNTRY / REALISED REPAIR / COUNTERFACTUAL CROSS-POLLINATION
--
-- This owner applies CounterfactualRealisedRepairExact to the existing Country,
-- terra-nullius, Billy/HRC, Two-Eyed Seeing and POSIWID surfaces.
--
-- Source boundary:
--   * Mabo/terra-nullius propositions remain owned upstream;
--   * Billy/HRC remedy propositions remain Committee-owned upstream;
--   * Australian implementation statements remain State-owned upstream;
--   * Two-Eyed Seeing/Kimmerer sources remain source-bounded upstream;
--   * the counterfactual worlds and causal-search obligations below are
--     SensibLaw/DASHI model constructions, not historical facts.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CounterfactualRealisedRepairExact as RepairCF
import DASHI.Core.CounterfactualModelContractExact as Counterfactual
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawTerraNulliusJuridicalHumanityOperationalEquivalenceExact as Humanity
import DASHI.Cognition.PNF.SensibLawTerraNulliusTwoEyedSystemContinuityExact as Continuity
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Remedy
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Country
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK

------------------------------------------------------------------------
-- 1. Foundational relation correction is positive, not label deletion.
------------------------------------------------------------------------

terraNulliusRelationCorrection : RepairCF.CorrectiveInterventionMeaning
terraNulliusRelationCorrection = RepairCF.corrective-intervention-meaning
  "foundational Crown-acquisition relation classifies Indigenous law, sovereignty, occupancy and proprietorship as non-constitutive for the acquiring legal order"
  "counterfactual relation preserves Indigenous law/sovereignty/Country/community authority as independently constitutive rather than requiring Crown creation or recognition"
  "SensibLaw counterfactual relation correction; not a claim that this counterfactual historically occurred"
  false refl
  true refl

terraNulliusClassificationStillStrong :
  Humanity.classify Humanity.terraNulliusCriterion
  ≡ Humanity.juridicallyNonHumanNonconstitutive
terraNulliusClassificationStillStrong = refl

terraNulliusDeniedConstitutiveLegalHumanity :
  Humanity.legallyConstitutiveHumanityDenied
    Humanity.terraNulliusJuridicalNonHumanityReading ≡ true
terraNulliusDeniedConstitutiveLegalHumanity = refl

------------------------------------------------------------------------
-- Counterfactual Country outcomes.  These are finite model states, not claims
-- about the uniquely correct historical alternate Australia.
------------------------------------------------------------------------

data CountryCorrectedWorld : Set where
  correctedOrderWithLandAuthority : CountryCorrectedWorld
  correctedOrderWithoutMaterialTransfer : CountryCorrectedWorld


data CountryRepairOutcome : Set where
  communityAuthorityAndCountryControlRealised : CountryRepairOutcome
  juridicalRecognitionWithoutMaterialCountryControl : CountryRepairOutcome


data CountryWorldAdmissible : CountryCorrectedWorld → Set where
  landAuthorityWorldAdmissible : CountryWorldAdmissible correctedOrderWithLandAuthority
  noMaterialTransferWorldAdmissible : CountryWorldAdmissible correctedOrderWithoutMaterialTransfer

countryOutcome : CountryCorrectedWorld → CountryRepairOutcome
countryOutcome correctedOrderWithLandAuthority = communityAuthorityAndCountryControlRealised
countryOutcome correctedOrderWithoutMaterialTransfer = juridicalRecognitionWithoutMaterialCountryControl

data CommunityAcceptableCountryOutcome : CountryRepairOutcome → Set where
  landAuthorityOutcomeAccepted :
    CommunityAcceptableCountryOutcome communityAuthorityAndCountryControlRealised

countryCounterfactualFibre : RepairCF.CorrectedWorldFibre
countryCounterfactualFibre = RepairCF.corrected-world-fibre
  CountryCorrectedWorld
  CountryRepairOutcome
  CountryWorldAdmissible
  countryOutcome
  CommunityAcceptableCountryOutcome
  terraNulliusRelationCorrection
  "upstream Mabo/terra-nullius source map + SensibLaw two-order counterfactual model"
  "consumer: realised transformation of Country/community authority, not doctrinal relabelling alone"

countryCounterfactualCurrentlyUnderidentified :
  RepairCF.CounterfactualRepairUnderidentification countryCounterfactualFibre
countryCounterfactualCurrentlyUnderidentified = RepairCF.counterfactual-repair-underidentification
  correctedOrderWithLandAuthority
  correctedOrderWithoutMaterialTransfer
  landAuthorityWorldAdmissible
  noMaterialTransferWorldAdmissible
  landAuthorityOutcomeAccepted
  (λ ())

------------------------------------------------------------------------
-- The underidentification is substantive: rejection/recognition alone does not
-- identify whether land/Country control and community authority change.
------------------------------------------------------------------------

currentLandCountryControlStillOpen :
  Continuity.currentCoordinateState Continuity.landCountryControl
  ≡ Continuity.open
currentLandCountryControlStillOpen = refl

currentCommunityAuthorityStillOpen :
  Continuity.currentCoordinateState Continuity.communityAuthorityBearing
  ≡ Continuity.open
currentCommunityAuthorityStillOpen = refl

doctrinalRejectionCanCoexistWithStructuralContinuityRisk :
  Continuity.classifyTransformation Continuity.doctrinalRejectionOnlyFixture
  ≡ Continuity.structuralContinuityRisk
doctrinalRejectionCanCoexistWithStructuralContinuityRisk = refl

------------------------------------------------------------------------
-- 2. Billy/HRC effective-remedy counterfactual.
------------------------------------------------------------------------

billyRemedyCorrection : RepairCF.CorrectiveInterventionMeaning
billyRemedyCorrection = RepairCF.corrective-intervention-meaning
  "remedy finding/commitment exists while one or more required remedy coordinates remain unrealised or publicly unverified"
  "all Committee-specified remedy coordinates are actuated and tested against community-defined realised outcome with monitoring and corrective revision"
  "SensibLaw effective-remedy actuation counterfactual; Committee remedy content remains source-owned upstream"
  false refl
  true refl

data BillyCorrectedWorld : Set where
  fullyActuatedCommunityAdequate : BillyCorrectedWorld
  formalImplementationWithoutCommunityAdequacy : BillyCorrectedWorld


data BillyRealisedOutcome : Set where
  fullReparationRealised : BillyRealisedOutcome
  declaredOrChannelUseWithoutFullReparation : BillyRealisedOutcome


data BillyWorldAdmissible : BillyCorrectedWorld → Set where
  fullActuationWorldAdmissible : BillyWorldAdmissible fullyActuatedCommunityAdequate
  formalOnlyWorldAdmissible : BillyWorldAdmissible formalImplementationWithoutCommunityAdequacy

billyOutcome : BillyCorrectedWorld → BillyRealisedOutcome
billyOutcome fullyActuatedCommunityAdequate = fullReparationRealised
billyOutcome formalImplementationWithoutCommunityAdequacy = declaredOrChannelUseWithoutFullReparation

data CommunityAcceptableBillyOutcome : BillyRealisedOutcome → Set where
  fullReparationAccepted : CommunityAcceptableBillyOutcome fullReparationRealised

billyCounterfactualFibre : RepairCF.CorrectedWorldFibre
billyCounterfactualFibre = RepairCF.corrected-world-fibre
  BillyCorrectedWorld
  BillyRealisedOutcome
  BillyWorldAdmissible
  billyOutcome
  CommunityAcceptableBillyOutcome
  billyRemedyCorrection
  "Human Rights Committee Billy Views + State implementation sources remain separately owned upstream"
  "consumer: actual effective remedy/full reparation, including community-defined outcome and correction"

billyCounterfactualCurrentlyUnderidentified :
  RepairCF.CounterfactualRepairUnderidentification billyCounterfactualFibre
billyCounterfactualCurrentlyUnderidentified = RepairCF.counterfactual-repair-underidentification
  fullyActuatedCommunityAdequate
  formalImplementationWithoutCommunityAdequacy
  fullActuationWorldAdmissible
  formalOnlyWorldAdmissible
  fullReparationAccepted
  (λ ())

currentPublicFullReparationStillOpen :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
currentPublicFullReparationStillOpen = refl

compensationStillNeedsReceipt :
  Billy.publicImplementationState Billy.adequateCompensation
  ≡ Billy.publicReceiptNotRecovered
compensationStillNeedsReceipt = refl

noAutomaticDomesticExecutionWrit :
  Billy.mechanismStrength Billy.directTreatyBodyDomesticExecutionWrit
  ≡ Billy.unavailableByDefault
noAutomaticDomesticExecutionWrit = refl

sourceBackedNumericImplementationOddsAreNotManufactured : Bool
sourceBackedNumericImplementationOddsAreNotManufactured = false

------------------------------------------------------------------------
-- 3. Two-Eyed Seeing: counterfactual evaluation is plural, not fused.
------------------------------------------------------------------------

sharedObservationDoesNotFuseKnowledgeHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
sharedObservationDoesNotFuseKnowledgeHistory = refl

extractedPropositionDoesNotRecoverCommunityAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedPropositionDoesNotRecoverCommunityAuthority = IK.propositionCannotRecoverAuthority

stateObservationDoesNotExhaustCommunityOutcome :
  Country.stateObservationExhaustsCommunityOutcome
    Country.canonicalBraidedRemedyAssessment ≡ false
stateObservationDoesNotExhaustCommunityOutcome = refl

communityOutcomeMayReopenImplementation :
  Country.communityOutcomeCanReopenImplementation
    Country.canonicalBraidedRemedyAssessment ≡ true
communityOutcomeMayReopenImplementation = refl

------------------------------------------------------------------------
-- 4. POSIWID: observed operation constrains the actual-world side, but does not
-- by itself identify the counterfactual world or causal effect.
------------------------------------------------------------------------

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

realisedOperationCanClassifyWhatSystemDoes :
  POSIWID.observedOperationMayClassifyWhatSystemDoes posiwidBoundary ≡ true
realisedOperationCanClassifyWhatSystemDoes = refl

declaredPurposeDoesNotOverrideRealisedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
declaredPurposeDoesNotOverrideRealisedEffect = refl

operationDoesNotProveIntent :
  POSIWID.observedOperationProvesSubjectiveIntent posiwidBoundary ≡ false
operationDoesNotProveIntent = refl

------------------------------------------------------------------------
-- Reverse-search schedule.
------------------------------------------------------------------------

data CountryCounterfactualQuestion : Set where
  butForJuridicalNonConstitution : CountryCounterfactualQuestion
  butForFailureToActuateBillyRemedy : CountryCounterfactualQuestion


needs : CountryCounterfactualQuestion → List RepairCF.CounterfactualRepairNeed
needs butForJuridicalNonConstitution =
  RepairCF.acquireAdmissibleCorrectedWorlds
  ∷ RepairCF.acquireHeldFixedJustification
  ∷ RepairCF.acquireOutcomeComparison
  ∷ RepairCF.acquireCausalIdentification
  ∷ RepairCF.acquireAffectedCommunityOutcomeReceipt
  ∷ RepairCF.acquireIndependentComparatorReceipt
  ∷ []
needs butForFailureToActuateBillyRemedy =
  RepairCF.acquireAdmissibleCorrectedWorlds
  ∷ RepairCF.acquireOutcomeComparison
  ∷ RepairCF.acquireCausalIdentification
  ∷ RepairCF.acquireAffectedCommunityOutcomeReceipt
  ∷ RepairCF.acquireIndependentComparatorReceipt
  ∷ []

------------------------------------------------------------------------
-- Cross-PR compatibility receipt: #791 and this owner share a donor, not a
-- doctrine or source authority.
------------------------------------------------------------------------

record LegalButForCrossPollinationBoundary : Set where
  constructor legal-but-for-cross-pollination-boundary
  field
    sharedGenericCounterfactualContract : Bool
    sharedGenericCounterfactualContractIsTrue :
      sharedGenericCounterfactualContract ≡ true
    importsLegalFactualCausationDoctrine : Bool
    importsLegalFactualCausationDoctrineIsFalse :
      importsLegalFactualCausationDoctrine ≡ false
    historicalStructuralCounterfactualEqualsTortButFor : Bool
    historicalStructuralCounterfactualEqualsTortButForIsFalse :
      historicalStructuralCounterfactualEqualsTortButFor ≡ false
    remedyActuationCounterfactualEqualsLiability : Bool
    remedyActuationCounterfactualEqualsLiabilityIsFalse :
      remedyActuationCounterfactualEqualsLiability ≡ false
    compatibilityReference : String

open LegalButForCrossPollinationBoundary public

canonicalLegalButForCrossPollinationBoundary : LegalButForCrossPollinationBoundary
canonicalLegalButForCrossPollinationBoundary = legal-but-for-cross-pollination-boundary
  true refl
  false refl
  false refl
  false refl
  "Cross-pollination with PR #791: both reuse DASHI.Core.CounterfactualModelContractExact; this owner does not import or duplicate LegalFactualCausationButForExact."

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data MaboRejectionIdentifiesDecolonialCounterfactual : Set where
data HRCFindingIdentifiesImplementationCounterfactual : Set where
data POSIWIDIdentifiesCausalCounterfactual : Set where
data StateReportDefinesCommunityCounterfactualOutcome : Set where
data ButForDifferenceTransfersCommunityAuthority : Set where

maboRejectionDoesNotIdentifyCounterfactual :
  MaboRejectionIdentifiesDecolonialCounterfactual → ⊥
maboRejectionDoesNotIdentifyCounterfactual ()

hrcFindingDoesNotIdentifyImplementationCounterfactual :
  HRCFindingIdentifiesImplementationCounterfactual → ⊥
hrcFindingDoesNotIdentifyImplementationCounterfactual ()

posiwidDoesNotIdentifyCounterfactualByItself : POSIWIDIdentifiesCausalCounterfactual → ⊥
posiwidDoesNotIdentifyCounterfactualByItself ()

stateReportDoesNotDefineCommunityCounterfactualOutcome :
  StateReportDefinesCommunityCounterfactualOutcome → ⊥
stateReportDoesNotDefineCommunityCounterfactualOutcome ()

butForDoesNotTransferCommunityAuthority : ButForDifferenceTransfersCommunityAuthority → ⊥
butForDoesNotTransferCommunityAuthority ()
