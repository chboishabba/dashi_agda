module DASHI.Ontology.NORAReviewPerspectiveProjectionExact where

------------------------------------------------------------------------
-- NORA is an external ontology mapping and review tool by Éder Porto.
-- Its five planned UI choices are NOT mathematical truth values.
-- The original research, sixfold/tetralemma and C2/C3 owners retain custody.
-- This local module is a finite, non-promoting review projection.
-- No real NORA export, source assertion or public Wikidata edit is certified.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import Base369
import DASHI.Algebra.SixfoldLogic as Six
import DASHI.Algebra.TetralemmaBridge as Tetra
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.ComputerScience.BalancedTernaryC2C3DihedralCodecBridgeExact as Dihedral
import DASHI.Foundations.SSPTritCarrier as SSP

-- A reviewer action and an assertion about source evidence are distinct axes.
data NORAChoice : Set where
  valid invalid ambiguous manualSearch modelingGap : NORAChoice

data ChoiceKind : Set where
  judgement unresolvedJudgement acquisitionRequest modelResidual : ChoiceKind

choiceKind : NORAChoice → ChoiceKind
choiceKind valid = judgement
choiceKind invalid = judgement
choiceKind ambiguous = unresolvedJudgement
choiceKind manualSearch = acquisitionRequest
choiceKind modelingGap = modelResidual

searchIsAnAction : choiceKind manualSearch ≡ acquisitionRequest
searchIsAnAction = refl

gapIsAResidual : choiceKind modelingGap ≡ modelResidual
gapIsAResidual = refl

validIsNotAnAcquisition : choiceKind valid ≡ acquisitionRequest → ⊥
validIsNotAnAcquisition ()

-- Retain attributed source, observer, review and consumer identity explicitly.
record SituatedNORAReview : Set where
  constructor situatedNoraReview
  field
    candidateRef : String
    sourceRevisionRef : String
    sourceAttributionRef : String
    reviewerRef : String
    standpointRef : String
    consumerRef : String
    choice : NORAChoice
    sixfoldQualification : Six.Stage6
    supportPosition : Tetra.TetralemmaPosition

open SituatedNORAReview public

reviewChoice : SituatedNORAReview → NORAChoice
reviewChoice = choice

support : SituatedNORAReview → Tetra.TetralemmaPosition
support = supportPosition

qualification : SituatedNORAReview → Six.Stage6
qualification = sixfoldQualification

-- NORA's ambiguous UI value cannot determine both vs neither evidence.
data SupportShape : Set where
  conflictingSupport noEvidence : SupportShape

supportShape : SupportShape → Tetra.TetralemmaPosition
supportShape conflictingSupport = Tetra.both
supportShape noEvidence = Tetra.neither

noraAmbiguity : SupportShape → NORAChoice
noraAmbiguity conflictingSupport = ambiguous
noraAmbiguity noEvidence = ambiguous

ambiguousHidesDistinctSupport :
  Consumer.ConsumerNonDescentWitness noraAmbiguity supportShape
ambiguousHidesDistinctSupport =
  Consumer.consumerNonDescentWitness
    conflictingSupport noEvidence refl (λ ())

ambiguousIsNotSufficientForSupport :
  Consumer.ConsumerSufficient noraAmbiguity supportShape → ⊥
ambiguousIsNotSufficientForSupport =
  Consumer.nonDescentWitnessBlocksSufficiency ambiguousHidesDistinctSupport

ambiguousCannotFactorThroughSupport :
  Consumer.FactorsThrough noraAmbiguity supportShape → ⊥
ambiguousCannotFactorThroughSupport =
  Consumer.nonDescentWitnessBlocksFactorization ambiguousHidesDistinctSupport

-- An invalid decision is consumer-local, not a universal refutation.
data QueryConsumer : Set where
  coarseDisplay detailedSourceAudit : QueryConsumer

consumerDecision : QueryConsumer → NORAChoice
consumerDecision coarseDisplay = valid
consumerDecision detailedSourceAudit = invalid

localValid : consumerDecision coarseDisplay ≡ valid
localValid = refl

localInvalid : consumerDecision detailedSourceAudit ≡ invalid
localInvalid = refl

-- Sixfold logic is retained as a separate qualification, not C6 identity.
reviewWithQualification :
  (r : SituatedNORAReview) → Six.Stage6 → SituatedNORAReview
reviewWithQualification r tone =
  situatedNoraReview
    (candidateRef r)
    (sourceRevisionRef r)
    (sourceAttributionRef r)
    (reviewerRef r)
    (standpointRef r)
    (consumerRef r)
    (choice r)
    tone
    (supportPosition r)

qualificationDoesNotRewriteReview :
  (r : SituatedNORAReview) (tone : Six.Stage6) →
  reviewChoice (reviewWithQualification r tone) ≡ reviewChoice r
qualificationDoesNotRewriteReview r tone = refl

qualificationDoesNotRewriteSupport :
  (r : SituatedNORAReview) (tone : Six.Stage6) →
  support (reviewWithQualification r tone) ≡ support r
qualificationDoesNotRewriteSupport r tone = refl

-- Reuse exact finite C2/C3 laws. These do not act on NORA review decisions.
finiteDihedralCompatibilityReused :
  (t : SSP.SSPTrit) →
  Dihedral.antipode (Dihedral.cycle (Dihedral.antipode t))
  ≡ Dihedral.cycleInverse t
finiteDihedralCompatibilityReused = Dihedral.antipodeConjugatesCycleToInverse

sixfoldRotationReused :
  (tone : Six.Stage6) →
  Six.hexTone (Six.next6 tone) ≡ Base369.rotateHex (Six.hexTone tone)
sixfoldRotationReused = Six.hexTone-next
