module DASHI.Cognition.PNF.SensibLawMaboRecognitionBasisDiscriminatorClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboBrennanDawsonIssueResidualLiveExact as Mabo
import DASHI.Cognition.PNF.SensibLawMaboRecognitionBasisAuthorityEvidenceExact as Authority

------------------------------------------------------------------------
-- TARGETED REVERSE-SEARCH REFINEMENT
------------------------------------------------------------------------

data RecognitionBasisState : Set where
  broadRecognitionBasisOpen
  sharedAuthorityRolesRecovered
  authorityInterpretationResidual
  recognitionBasisPartiallyIdentified
  : RecognitionBasisState

record RecognitionBasisDiscriminatorReceipt : Set where
  constructor recognitionBasisDiscriminatorReceipt
  field
    residual : Mabo.MaboControversyResidual
    amoduContrast : Authority.SharedAuthorityUseContrast Authority.brennanAmoduUse Authority.dawsonAmoduUse
    calderContrast : Authority.SharedAuthorityUseContrast Authority.brennanCalderUse Authority.dawsonCalderUse
    priorState : RecognitionBasisState
    resultingState : RecognitionBasisState
    compatibleBrennanBasis : List Authority.AuthorityUseKind
    compatibleDawsonBasis : List Authority.AuthorityUseKind
    nextQuestion : String
    wholeJudgmentRescanRequired : Bool
    wholeJudgmentRescanRequiredIsFalse : wholeJudgmentRescanRequired ≡ false
    exactFinalHoldingClaimed : Bool
    exactFinalHoldingClaimedIsFalse : exactFinalHoldingClaimed ≡ false
open RecognitionBasisDiscriminatorReceipt public

recognitionBasisReceipt : RecognitionBasisDiscriminatorReceipt
recognitionBasisReceipt = recognitionBasisDiscriminatorReceipt
  Mabo.brennanDawsonResidual
  Authority.amoduUseContrast
  Authority.calderUseContrast
  broadRecognitionBasisOpen
  recognitionBasisPartiallyIdentified
  ( Authority.continuityRuleUse
  ∷ Authority.radicalTitleCompatibilityUse
  ∷ [])
  ( Authority.recognitionDoctrineUse
  ∷ Authority.evidentialRecognitionUse
  ∷ Authority.authorityInterpretationUse
  ∷ [])
  "inspect the exact propositions for which Brennan treats continuity as the preferable rule and Dawson treats Crown recognition/acquiescence as necessary, then compare their readings of Calder and Amodu Tijani"
  false refl false refl

resultNarrowsWithoutWholeRescan : resultingState recognitionBasisReceipt ≡ recognitionBasisPartiallyIdentified
resultNarrowsWithoutWholeRescan = refl

------------------------------------------------------------------------
-- Partial identification: the evidence narrows the residual but does not
-- manufacture a single globally exhaustive theory of either judgment.
------------------------------------------------------------------------

data RecognitionBasisClosureGoal : Set where
  listCompatibleRecognitionBases
  identifyExactExhaustiveJurisprudentialTheory
  identifySharedAuthorityRole
  : RecognitionBasisClosureGoal

data RecognitionBasisGoalStatus : Set where
  goalClosed
  goalOpen
  : RecognitionBasisGoalStatus

goalStatus : RecognitionBasisClosureGoal → RecognitionBasisDiscriminatorReceipt → RecognitionBasisGoalStatus
goalStatus listCompatibleRecognitionBases receipt = goalClosed
goalStatus identifyExactExhaustiveJurisprudentialTheory receipt = goalOpen
goalStatus identifySharedAuthorityRole receipt = goalOpen

compatibleBasisConsumerCloses : goalStatus listCompatibleRecognitionBases recognitionBasisReceipt ≡ goalClosed
compatibleBasisConsumerCloses = refl

exactTheoryConsumerRemainsOpen : goalStatus identifyExactExhaustiveJurisprudentialTheory recognitionBasisReceipt ≡ goalOpen
exactTheoryConsumerRemainsOpen = refl

sharedAuthorityRoleConsumerRemainsOpen : goalStatus identifySharedAuthorityRole recognitionBasisReceipt ≡ goalOpen
sharedAuthorityRoleConsumerRemainsOpen = refl

------------------------------------------------------------------------
-- Next targeted source probes.
------------------------------------------------------------------------

data RecognitionBasisProbe : Set where
  inspectBrennanParas54To61
  inspectDawsonParas7To16
  inspectCalderHallAndJudsonSplit
  inspectAmoduTijaniRecognitionAndRadicalTitlePassages
  : RecognitionBasisProbe

nextProbes : RecognitionBasisDiscriminatorReceipt → List RecognitionBasisProbe
nextProbes receipt =
  inspectBrennanParas54To61
  ∷ inspectDawsonParas7To16
  ∷ inspectCalderHallAndJudsonSplit
  ∷ inspectAmoduTijaniRecognitionAndRadicalTitlePassages
  ∷ []

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data SharedCitationClosesSharedMeaning : Set where
data PartialIdentificationMeansExactTheory : Set where
data AuthorityUseContrastMeansAuthorityConflict : Set where
data TargetedProbeMeansFinalAdjudication : Set where

sharedCitationDoesNotCloseMeaning : SharedCitationClosesSharedMeaning → ⊥
sharedCitationDoesNotCloseMeaning ()
partialIdentificationDoesNotMeanExactTheory : PartialIdentificationMeansExactTheory → ⊥
partialIdentificationDoesNotMeanExactTheory ()
authorityUseContrastDoesNotMeanAuthorityConflict : AuthorityUseContrastMeansAuthorityConflict → ⊥
authorityUseContrastDoesNotMeanAuthorityConflict ()
targetedProbeDoesNotMeanFinalAdjudication : TargetedProbeMeansFinalAdjudication → ⊥
targetedProbeDoesNotMeanFinalAdjudication ()
