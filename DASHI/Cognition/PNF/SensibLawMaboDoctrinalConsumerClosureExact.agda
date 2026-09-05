module DASHI.Cognition.PNF.SensibLawMaboDoctrinalConsumerClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact as Minimal
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalCutsetExact as Cutset

------------------------------------------------------------------------
-- Consumer-relative closure: source-map questions may close before final
-- doctrinal interpretation.
------------------------------------------------------------------------

data DoctrinalConsumerGoal : Set where
  listSourceBackedContinuityPropositions
  listSourceBackedExtinguishmentPropositions
  identifyRecognitionConditionInterpretation
  identifyRecognitionEvidenceBasis
  adjudicateFinalContinuityDoctrine
  adjudicateUnifiedRecognitionDoctrine
  : DoctrinalConsumerGoal

data GoalStatus : Set where goalOpen goalClosed : GoalStatus

goalStatus : DoctrinalConsumerGoal → Cutset.MinimalDoctrinalCutset → GoalStatus
goalStatus listSourceBackedContinuityPropositions c with Cutset.sourceIdentityClosed c
... | false = goalOpen
... | true with Cutset.existenceContinuityClosed c
...   | false = goalOpen
...   | true = goalClosed
goalStatus listSourceBackedExtinguishmentPropositions c with Cutset.sourceIdentityClosed c
... | false = goalOpen
... | true with Cutset.extinguishmentClosed c
...   | false = goalOpen
...   | true = goalClosed
goalStatus identifyRecognitionConditionInterpretation c with Cutset.recognitionConditionClosed c
... | false = goalOpen
... | true with Cutset.authorityInterpretationClosed c
...   | false = goalOpen
...   | true = goalClosed
goalStatus identifyRecognitionEvidenceBasis c with Cutset.recognitionEvidenceClosed c
... | false = goalOpen
... | true = goalClosed
goalStatus adjudicateFinalContinuityDoctrine c with Cutset.existenceContinuityClosed c
... | false = goalOpen
... | true with Cutset.authorityInterpretationClosed c
...   | false = goalOpen
...   | true = goalClosed
goalStatus adjudicateUnifiedRecognitionDoctrine c with Cutset.existenceContinuityClosed c
... | false = goalOpen
... | true with Cutset.recognitionConditionClosed c
...   | false = goalOpen
...   | true with Cutset.recognitionEvidenceClosed c
...     | false = goalOpen
...     | true with Cutset.extinguishmentClosed c
...       | false = goalOpen
...       | true with Cutset.authorityInterpretationClosed c
...         | false = goalOpen
...         | true = goalClosed

continuitySourceMapClosesAfterVerification :
  goalStatus listSourceBackedContinuityPropositions Cutset.postHallVerificationCutset ≡ goalClosed
continuitySourceMapClosesAfterVerification = refl

extinguishmentSourceMapClosesAfterVerification :
  goalStatus listSourceBackedExtinguishmentPropositions Cutset.postHallVerificationCutset ≡ goalClosed
extinguishmentSourceMapClosesAfterVerification = refl

finalContinuityDoctrineStillOpen :
  goalStatus adjudicateFinalContinuityDoctrine Cutset.postHallVerificationCutset ≡ goalOpen
finalContinuityDoctrineStillOpen = refl

recognitionConditionInterpretationStillOpen :
  goalStatus identifyRecognitionConditionInterpretation Cutset.postHallVerificationCutset ≡ goalOpen
recognitionConditionInterpretationStillOpen = refl

recognitionEvidenceBasisStillOpen :
  goalStatus identifyRecognitionEvidenceBasis Cutset.postHallVerificationCutset ≡ goalOpen
recognitionEvidenceBasisStillOpen = refl

unifiedDoctrineStillOpen :
  goalStatus adjudicateUnifiedRecognitionDoctrine Cutset.postHallVerificationCutset ≡ goalOpen
unifiedDoctrineStillOpen = refl

data SourceMapClosureMeansFinalDoctrine : Set where
data VerifiedQuotationMeansAdoptedRule : Set where
data NarrowConsumerClosureClosesUnifiedDoctrine : Set where

sourceMapClosureDoesNotMeanFinalDoctrine : SourceMapClosureMeansFinalDoctrine → ⊥
sourceMapClosureDoesNotMeanFinalDoctrine ()
verifiedQuotationDoesNotMeanAdoptedRule : VerifiedQuotationMeansAdoptedRule → ⊥
verifiedQuotationDoesNotMeanAdoptedRule ()
narrowClosureDoesNotCloseUnifiedDoctrine : NarrowConsumerClosureClosesUnifiedDoctrine → ⊥
narrowClosureDoesNotCloseUnifiedDoctrine ()
