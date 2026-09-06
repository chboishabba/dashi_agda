module DASHI.Core.FibreRefinementExperimentSelectionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.ProjectionHierarchyCompatibleFibreBidiExact as Projection
import DASHI.Core.ExperimentalCoordinateDesignExact as Design

data RefinementGrade : Set where
  noCertifiedRefinement weakRefinement strictRefinement : RefinementGrade

record ExperimentRefinementReceipt {Hidden Experiment : Set}
    (prior : Bidi.ResidualFibre Hidden) : Set₁ where
  constructor experiment-refinement-receipt
  field
    experiment : Experiment
    posterior : Bidi.ResidualFibre Hidden
    refines : Bidi.FibreRefines posterior prior
    grade : RefinementGrade
    strictWitness : grade ≡ strictRefinement → Σ Hidden (λ hidden → prior hidden × ¬ (posterior hidden))
    experimentReference : String
    calibrationReference : String
open ExperimentRefinementReceipt public

record FibreRefinementChoice {Hidden Experiment : Set}
    (prior : Bidi.ResidualFibre Hidden) : Set₁ where
  constructor fibre-refinement-choice
  field
    selected : ExperimentRefinementReceipt {Hidden} {Experiment} prior
    selectionReason : String
    selectionUsesNumericIdentificationPercent : Bool
    selectionUsesNumericIdentificationPercentIsFalse : selectionUsesNumericIdentificationPercent ≡ false
open FibreRefinementChoice public

chooseStrictRefinement :
  ∀ {Hidden Experiment : Set} {prior : Bidi.ResidualFibre Hidden} →
  (receipt : ExperimentRefinementReceipt {Hidden} {Experiment} prior) →
  grade receipt ≡ strictRefinement → FibreRefinementChoice prior
chooseStrictRefinement receipt strict = fibre-refinement-choice receipt
  "selected experiment carries a strict compatible-fibre refinement witness" false refl

strictReceiptEliminatesPriorCandidate :
  ∀ {Hidden Experiment : Set} {prior : Bidi.ResidualFibre Hidden}
    (receipt : ExperimentRefinementReceipt {Hidden} {Experiment} prior) →
  grade receipt ≡ strictRefinement →
  Σ Hidden (λ hidden → prior hidden × ¬ (posterior receipt hidden))
strictReceiptEliminatesPriorCandidate receipt strict = strictWitness receipt strict

data ToyExperiment : Set where addMiddleObservation addFineObservation : ToyExperiment

coarseToMiddleReceipt : ExperimentRefinementReceipt {Experiment = ToyExperiment} Projection.coarseFibre
coarseToMiddleReceipt = experiment-refinement-receipt addMiddleObservation Projection.middleFibre
  Projection.middleRefinesCoarse strictRefinement
  (λ _ → Projection.witness Projection.middleStrictlyRefinesCoarse)
  "synthetic middle observation" "exact finite projection-hierarchy calibration"

middleToFineReceipt : ExperimentRefinementReceipt {Experiment = ToyExperiment} Projection.middleFibre
middleToFineReceipt = experiment-refinement-receipt addFineObservation Projection.fineFibre
  Projection.fineRefinesMiddle strictRefinement
  (λ _ → Projection.witness Projection.fineStrictlyRefinesMiddle)
  "synthetic fine observation" "exact finite projection-hierarchy calibration"

coarseExperimentEliminatesCandidate :
  Σ Projection.Hidden (λ hidden → Projection.coarseFibre hidden × ¬ (Projection.middleFibre hidden))
coarseExperimentEliminatesCandidate = strictReceiptEliminatesPriorCandidate coarseToMiddleReceipt refl

middleExperimentEliminatesCandidate :
  Σ Projection.Hidden (λ hidden → Projection.middleFibre hidden × ¬ (Projection.fineFibre hidden))
middleExperimentEliminatesCandidate = strictReceiptEliminatesPriorCandidate middleToFineReceipt refl

data CoordinateNameAloneProvesStrictRefinement : Set where
data StrictRefinementAutomaticallyClosesEveryConsumer : Set where
data FibreShrinkageAutomaticallyIdentifiesMechanism : Set where
coordinateNameAloneDoesNotProveStrictRefinement : CoordinateNameAloneProvesStrictRefinement → ⊥
coordinateNameAloneDoesNotProveStrictRefinement ()
strictRefinementDoesNotCloseEveryConsumer : StrictRefinementAutomaticallyClosesEveryConsumer → ⊥
strictRefinementDoesNotCloseEveryConsumer ()
fibreShrinkageDoesNotAutomaticallyIdentifyMechanism : FibreShrinkageAutomaticallyIdentifiesMechanism → ⊥
fibreShrinkageDoesNotAutomaticallyIdentifyMechanism ()

record FibreRefinementSelectionBoundary : Set where
  constructor fibre-refinement-selection-boundary
  field
    strictSelectionCarriesEliminatedCandidate : Bool
    numericIdentificationFractionRequired : Bool
    coordinateNameIsRefinementProof : Bool
    strictRefinementIsGlobalClosure : Bool
canonicalFibreRefinementSelectionBoundary : FibreRefinementSelectionBoundary
canonicalFibreRefinementSelectionBoundary = fibre-refinement-selection-boundary true false false false
