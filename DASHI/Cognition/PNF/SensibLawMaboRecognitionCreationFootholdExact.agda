module DASHI.Cognition.PNF.SensibLawMaboRecognitionCreationFootholdExact where

------------------------------------------------------------------------
-- MABO: RECOGNITION OF PRE-EXISTING RIGHTS VS CREATION OF A NEW REGIME
--
-- Primary / stable sources:
--   * Mabo v Queensland (No 2) [1992] HCA 23; 175 CLR 1.
--   * Sir Gerard Brennan, "Aboriginal Land Claims - An Australian Perspective",
--     High Court of Australia speech archive:
--     https://www.hcourt.gov.au/sites/default/files/assets/publications/speeches/former-justices/brennanj/brennanj_canada.htm
--   * Love v Commonwealth / Thoms v Commonwealth, Defendant's Further
--     Submissions, B43/2018, para 23-24, High Court of Australia:
--     https://www.hcourt.gov.au/assets/cases/02-Brisbane/b43-2018/Love-Thoms_Def_further_subs-2.pdf
--   * Mabo v Queensland (No 1) (1988) 166 CLR 186; [1988] HCA 69.
--   * Native Title Act 1993 (Cth), C2004A04665.
--
-- Source boundary:
--   The algebraic decomposition below is DASHI reconstruction. It captures the
--   structural move evidenced by Mabo without attributing the notation or every
--   intermediate proposition to Brennan J or later parties.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge

brennanRetrospectiveAuthority : Edge.SourceIdentity
brennanRetrospectiveAuthority = Edge.source-identity
  "Sir Gerard Brennan"
  "Aboriginal Land Claims - An Australian Perspective"
  "https://www.hcourt.gov.au/sites/default/files/assets/publications/speeches/former-justices/brennanj/brennanj_canada.htm"
  Edge.empiricalSource

maboNo1Authority : Edge.SourceIdentity
maboNo1Authority = Edge.source-identity
  "High Court of Australia"
  "Mabo v Queensland (No 1)"
  "[1988] HCA 69; 166 CLR 186"
  Edge.bindingPrecedent

------------------------------------------------------------------------
-- The key decomposition.
------------------------------------------------------------------------

data SovereigntyAcquired : Set where sovereignty-acquired : SovereigntyAcquired
data RadicalTitleAcquired : Set where radical-title-acquired : RadicalTitleAcquired
data CrownBeneficialOwnershipAllLand : Set where crown-beneficial-ownership-all-land : CrownBeneficialOwnershipAllLand
data PreExistingIndigenousLandRight : Set where pre-existing-right : PreExistingIndigenousLandRight
data ValidExtinguishment : Set where valid-extinguishment : ValidExtinguishment

sovereigntyToRadicalTitle : SovereigntyAcquired → RadicalTitleAcquired
sovereigntyToRadicalTitle sovereignty-acquired = radical-title-acquired

-- What is rejected is the *automatic implication*, not the logical possibility
-- of Crown beneficial ownership in some land under some other valid source.
data RadicalTitleAutomaticallyImpliesBeneficialOwnershipAllLand : Set where

radicalTitleDoesNotAutomaticallyGiveBeneficialOwnershipAllLand :
  RadicalTitleAutomaticallyImpliesBeneficialOwnershipAllLand → ⊥
radicalTitleDoesNotAutomaticallyGiveBeneficialOwnershipAllLand ()

record MaboFoothold : Set where
  constructor mabo-foothold
  field
    antecedentRightPredatesSovereignty : Bool
    sovereigntyQuestionItselfLeftIntact : Bool
    effectOfSovereigntyOnLandRightsJusticiable : Bool
    radicalTitleNotAutomaticBeneficialOwnership : Bool
    commonLawRecognitionAvailable : Bool
    newLegislativeRightRequiredForRecognition : Bool

open MaboFoothold public

canonicalMaboFoothold : MaboFoothold
canonicalMaboFoothold = mabo-foothold true true true true true false

maboRecognisesRatherThanLegislativelyCreates :
  newLegislativeRightRequiredForRecognition canonicalMaboFoothold ≡ false
maboRecognisesRatherThanLegislativelyCreates = refl

maboPreservesSovereigntyBoundary :
  sovereigntyQuestionItselfLeftIntact canonicalMaboFoothold ≡ true
maboPreservesSovereigntyBoundary = refl

------------------------------------------------------------------------
-- Common-law foothold search.
------------------------------------------------------------------------

data TransformationMode : Set where
  recognisePreExistingInterest
  reinterpretExistingCommonLaw
  incrementalCommonLawDevelopment
  construeExistingStatute
  constitutionalInvalidation
  requireNewLegislation
  internationalInterpretiveInputOnly
  : TransformationMode

record FootholdSearchResult : Set where
  constructor foothold-search-result
  field
    target : String
    apparentBlockingWeld : String
    proposedDecomposition : String
    mode : TransformationMode
    existingAuthority : Edge.SourceIdentity
    resultAlreadyEstablished : Bool
    furtherProofRequired : Bool

open FootholdSearchResult public

maboKnownPositive : FootholdSearchResult
maboKnownPositive = foothold-search-result
  "survival/recognition of pre-existing native title"
  "sovereignty acquired -> Crown beneficial ownership of all land"
  "sovereignty -> radical title; radical title does not itself extinguish every pre-existing Indigenous land right"
  recognisePreExistingInterest
  Edge.maboAuthority
  true
  false

climateCandidateSearch : FootholdSearchResult
climateCandidateSearch = foothold-search-result
  "candidate Commonwealth climate duty concerning specified physical injury/death"
  "one or more modern Australian negligence/public-authority duty gates"
  "test whether each apparently categorical no-duty edge is actually entailed at the asserted level of generality"
  incrementalCommonLawDevelopment
  Edge.pabaiAuthority
  false
  true

------------------------------------------------------------------------
-- Mabo No 1 -> Mabo No 2 -> Native Title Act interaction.
------------------------------------------------------------------------

data LegalLayer : Set where
  factLayer
  antecedentLegalOrderLayer
  commonLawLayer
  statuteLayer
  constitutionLayer
  judicialHoldingLayer
  laterLegislationLayer
  : LegalLayer

record LayerTransition : Set where
  constructor layer-transition
  field
    fromLayer : LegalLayer
    toLayer : LegalLayer
    proposition : String
    authority : Edge.SourceIdentity

open LayerTransition public

maboNo1ConstitutionalTransition : LayerTransition
maboNo1ConstitutionalTransition = layer-transition
  statuteLayer constitutionLayer
  "Queensland extinguishment legislation was tested against Commonwealth racial-discrimination legislation through constitutional inconsistency"
  maboNo1Authority

maboNo2CommonLawTransition : LayerTransition
maboNo2CommonLawTransition = layer-transition
  antecedentLegalOrderLayer commonLawLayer
  "common law can recognise pre-existing Indigenous land rights surviving sovereignty absent valid extinguishment"
  Edge.maboAuthority

nativeTitleActSystematisation : LayerTransition
nativeTitleActSystematisation = layer-transition
  judicialHoldingLayer laterLegislationLayer
  "Parliament enacted a statutory native-title system after Mabo recognition"
  Edge.nativeTitleActAuthority

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data JudicialRecognitionEqualsStatutoryCreation : Set where
data SovereigntyPreservedMeansPropertyConsequencesFrozen : Set where
data NormativeStrengthCreatesExistingLegalFoothold : Set where
data MaboFootholdAutomaticallyTransfersToClimateNegligence : Set where

recognitionIsNotStatutoryCreation : JudicialRecognitionEqualsStatutoryCreation → ⊥
recognitionIsNotStatutoryCreation ()

sovereigntyBoundaryDoesNotFreezeEveryConsequence : SovereigntyPreservedMeansPropertyConsequencesFrozen → ⊥
sovereigntyBoundaryDoesNotFreezeEveryConsequence ()

normativeStrengthDoesNotManufactureFoothold : NormativeStrengthCreatesExistingLegalFoothold → ⊥
normativeStrengthDoesNotManufactureFoothold ()

maboStructureDoesNotProveClimateDoctrine : MaboFootholdAutomaticallyTransfersToClimateNegligence → ⊥
maboStructureDoesNotProveClimateDoctrine ()
