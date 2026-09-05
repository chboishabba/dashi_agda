module DASHI.Cognition.PNF.SensibLawMaboRecognitionCoordinateFactorisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboBrennanDawsonIssueResidualLiveExact as Mabo
import DASHI.Cognition.PNF.SensibLawMaboRecognitionBasisAuthorityEvidenceExact as Authority
import DASHI.Cognition.PNF.SensibLawMaboRecognitionBasisDiscriminatorClosureExact as Closure

------------------------------------------------------------------------
-- FACTOR THE BROAD "RECOGNITION BASIS" RESIDUAL INTO DISTINCT LEGAL AXES.
--
-- The source-backed authority-use receipts motivate several different
-- questions which must not be collapsed into one recognition Boolean.
------------------------------------------------------------------------

data RecognitionCoordinate : Set where
  antecedentRightExistence
  continuityAcrossSovereignty
  radicalTitleCompatibility
  enforceabilityAgainstCrown
  crownRecognitionRequirement
  recognitionByCrownConduct
  evidentialInferenceOfRecognition
  authorityInterpretation
  : RecognitionCoordinate

record CoordinateQuestion : Set where
  constructor coordinateQuestion
  field
    coordinate : RecognitionCoordinate
    questionReference : String
open CoordinateQuestion public

continuityQuestion : CoordinateQuestion
continuityQuestion = coordinateQuestion continuityAcrossSovereignty
  "Does the antecedent native right/title survive the acquisition or change of sovereignty as a matter of legal continuity?"

enforceabilityQuestion : CoordinateQuestion
enforceabilityQuestion = coordinateQuestion enforceabilityAgainstCrown
  "Assuming antecedent rights continue, what legal relation makes them enforceable against or capable of burdening the Crown's title?"

recognitionQuestion : CoordinateQuestion
recognitionQuestion = coordinateQuestion crownRecognitionRequirement
  "Is Crown recognition a necessary juridical condition for the native interest to have legal effect against the Crown?"

recognitionConductQuestion : CoordinateQuestion
recognitionConductQuestion = coordinateQuestion recognitionByCrownConduct
  "Can Crown conduct, acquiescence or continued undisturbed occupation constitute or evidence the relevant recognition?"

------------------------------------------------------------------------
-- Reviewed authority use -> coordinate support is itself proof-relevant.
------------------------------------------------------------------------

record AuthorityCoordinateReceipt
    {proposition : Mabo.ReviewedJudicialProposition}
    (use : Authority.AuthorityUseReceipt proposition) : Set where
  constructor authorityCoordinateReceipt
  field
    supportedCoordinates : List RecognitionCoordinate
    reviewReference : String
    authorityUseAloneClosesCoordinate : Bool
    authorityUseAloneClosesCoordinateIsFalse : authorityUseAloneClosesCoordinate ≡ false
open AuthorityCoordinateReceipt public

brennanAmoduCoordinates : AuthorityCoordinateReceipt Authority.brennanAmoduUse
brennanAmoduCoordinates = authorityCoordinateReceipt
  (radicalTitleCompatibility ∷ enforceabilityAgainstCrown ∷ [])
  "reviewed classification: Brennan's Amodu Tijani use bears on native title qualifying/burdening radical title; this is distinct from proving all continuity or recognition propositions"
  false refl

brennanCalderCoordinates : AuthorityCoordinateReceipt Authority.brennanCalderUse
brennanCalderCoordinates = authorityCoordinateReceipt
  (antecedentRightExistence ∷ continuityAcrossSovereignty ∷ [])
  "reviewed classification: Brennan's Hall J/Calder use bears on antecedent Indigenous rights not depending on later grant/recognition and on continuity reasoning"
  false refl

dawsonAmoduCoordinates : AuthorityCoordinateReceipt Authority.dawsonAmoduUse
dawsonAmoduCoordinates = authorityCoordinateReceipt
  (crownRecognitionRequirement ∷ authorityInterpretation ∷ [])
  "reviewed classification: Dawson's Amodu Tijani use sits in the Crown-recognition analysis; this does not itself decide antecedent-right existence or continuity"
  false refl

dawsonCalderCoordinates : AuthorityCoordinateReceipt Authority.dawsonCalderUse
dawsonCalderCoordinates = authorityCoordinateReceipt
  (crownRecognitionRequirement ∷ recognitionByCrownConduct ∷ evidentialInferenceOfRecognition ∷ authorityInterpretation ∷ [])
  "reviewed classification: Dawson reads Calder through Crown recognition, including recognition evidenced/inferred from acquiescence and conduct"
  false refl

------------------------------------------------------------------------
-- A single authority can feed different coordinates in the two judgments.
------------------------------------------------------------------------

record SameAuthorityDifferentCoordinateReceipt : Set where
  constructor sameAuthorityDifferentCoordinateReceipt
  field
    authorityReference : String
    brennanCoordinates : List RecognitionCoordinate
    dawsonCoordinates : List RecognitionCoordinate
    sameAuthorityIdentity : Bool
    sameAuthorityIdentityIsTrue : sameAuthorityIdentity ≡ true
    coordinateFamiliesDiffer : Bool
    coordinateFamiliesDifferIsTrue : coordinateFamiliesDiffer ≡ true
    receiptReference : String
open SameAuthorityDifferentCoordinateReceipt public

calderCoordinateContrast : SameAuthorityDifferentCoordinateReceipt
calderCoordinateContrast = sameAuthorityDifferentCoordinateReceipt
  "authority:Calder-v-AG-BC-1973"
  (antecedentRightExistence ∷ continuityAcrossSovereignty ∷ [])
  (crownRecognitionRequirement ∷ recognitionByCrownConduct ∷ evidentialInferenceOfRecognition ∷ authorityInterpretation ∷ [])
  true refl true refl
  "same Calder authority identity; Brennan and Dawson uses are projected onto different legal coordinates"

amoduCoordinateContrast : SameAuthorityDifferentCoordinateReceipt
amoduCoordinateContrast = sameAuthorityDifferentCoordinateReceipt
  "authority:Amodu-Tijani-1921"
  (radicalTitleCompatibility ∷ enforceabilityAgainstCrown ∷ [])
  (crownRecognitionRequirement ∷ authorityInterpretation ∷ [])
  true refl true refl
  "same Amodu Tijani authority identity; Brennan use concerns radical-title compatibility while Dawson use concerns recognition doctrine"

------------------------------------------------------------------------
-- Query-indexed cutsets over the factorised residual.
------------------------------------------------------------------------

data RecognitionQuery : Set where
  identifyContinuityRule
  identifyCrownRecognitionRule
  identifyRecognitionByConductRule
  identifyEnforceabilityStructure
  identifyExactUnifiedTheory
  : RecognitionQuery

requiredCoordinates : RecognitionQuery → List RecognitionCoordinate
requiredCoordinates identifyContinuityRule =
  antecedentRightExistence ∷ continuityAcrossSovereignty ∷ []
requiredCoordinates identifyCrownRecognitionRule =
  crownRecognitionRequirement ∷ authorityInterpretation ∷ []
requiredCoordinates identifyRecognitionByConductRule =
  crownRecognitionRequirement ∷ recognitionByCrownConduct ∷ evidentialInferenceOfRecognition ∷ []
requiredCoordinates identifyEnforceabilityStructure =
  radicalTitleCompatibility ∷ enforceabilityAgainstCrown ∷ []
requiredCoordinates identifyExactUnifiedTheory =
  antecedentRightExistence ∷ continuityAcrossSovereignty ∷ radicalTitleCompatibility ∷ enforceabilityAgainstCrown ∷ crownRecognitionRequirement ∷ recognitionByCrownConduct ∷ evidentialInferenceOfRecognition ∷ authorityInterpretation ∷ []

------------------------------------------------------------------------
-- Partial-identification state generated from the current authority receipts.
------------------------------------------------------------------------

data CoordinateState : Set where
  coordinateUnassessed
  coordinateCandidateSupported
  coordinateResolved
  : CoordinateState

record FactorisedRecognitionState : Set where
  constructor factorisedRecognitionState
  field
    continuityState : CoordinateState
    enforceabilityState : CoordinateState
    recognitionRequirementState : CoordinateState
    recognitionConductState : CoordinateState
    exactUnifiedTheoryState : CoordinateState
    sourceReference : String
open FactorisedRecognitionState public

currentFactorisedState : FactorisedRecognitionState
currentFactorisedState = factorisedRecognitionState
  coordinateCandidateSupported
  coordinateCandidateSupported
  coordinateCandidateSupported
  coordinateCandidateSupported
  coordinateUnassessed
  "factorised from current Brennan/Dawson primary-text and reviewed Calder/Amodu authority-use receipts; no coordinate promoted to final adjudicative resolution"

------------------------------------------------------------------------
-- Important no-collapse results.
------------------------------------------------------------------------

data RecognitionByConductProvesContinuity : Set where
data ContinuityProvesRecognitionByConduct : Set where
data RadicalTitleCompatibilityProvesRecognitionRequirement : Set where
data SameAuthorityProvesSameCoordinate : Set where
data FactorisedCandidatesProveExactUnifiedTheory : Set where
\data RecognitionWordMeansSingleLegalCoordinate : Set where

recognitionByConductDoesNotProveContinuity : RecognitionByConductProvesContinuity → ⊥
recognitionByConductDoesNotProveContinuity ()

continuityDoesNotProveRecognitionByConduct : ContinuityProvesRecognitionByConduct → ⊥
continuityDoesNotProveRecognitionByConduct ()

radicalTitleCompatibilityDoesNotProveRecognitionRequirement : RadicalTitleCompatibilityProvesRecognitionRequirement → ⊥
radicalTitleCompatibilityDoesNotProveRecognitionRequirement ()

sameAuthorityDoesNotProveSameCoordinate : SameAuthorityProvesSameCoordinate → ⊥
sameAuthorityDoesNotProveSameCoordinate ()

factorisedCandidatesDoNotProveExactTheory : FactorisedCandidatesProveExactUnifiedTheory → ⊥
factorisedCandidatesDoNotProveExactTheory ()

recognitionWordDoesNotMeanOneCoordinate : RecognitionWordMeansSingleLegalCoordinate → ⊥
recognitionWordDoesNotMeanOneCoordinate ()

------------------------------------------------------------------------
-- Cross-pollination back to the prior coarse residual.
------------------------------------------------------------------------

coarseResidualWasOnlyPartialIdentification :
  Closure.resultingState Closure.recognitionBasisReceipt ≡ Closure.recognitionBasisPartiallyIdentified
coarseResidualWasOnlyPartialIdentification = refl

record RecognitionFactorisationBoundary : Set where
  constructor recognitionFactorisationBoundary
  field
    broadRecognitionResidualFactorised : Bool
    broadRecognitionResidualFactorisedIsTrue : broadRecognitionResidualFactorised ≡ true
    sameAuthoritySameCoordinate : Bool
    sameAuthoritySameCoordinateIsFalse : sameAuthoritySameCoordinate ≡ false
    recognitionByConductEqualsContinuity : Bool
    recognitionByConductEqualsContinuityIsFalse : recognitionByConductEqualsContinuity ≡ false
    currentReceiptsResolveExactUnifiedTheory : Bool
    currentReceiptsResolveExactUnifiedTheoryIsFalse : currentReceiptsResolveExactUnifiedTheory ≡ false

canonicalRecognitionFactorisationBoundary : RecognitionFactorisationBoundary
canonicalRecognitionFactorisationBoundary =
  recognitionFactorisationBoundary true refl false refl false refl false refl
