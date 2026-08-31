module DASHI.Core.BidiResidualApproximationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.ResidualObligationPropagationExact as Residual

------------------------------------------------------------------------
-- GENERIC BIDI RESIDUAL APPROXIMATION
--
-- A failed exact identification is not treated as an information vacuum.
-- Instead, observations and independently warranted constraints define an
-- admissible hidden-state fibre. Additional evidence may monotonically shrink
-- that fibre even when it does not collapse it to a point.
------------------------------------------------------------------------

private
  variable
    Evidence Hidden Prediction Measurement : Set

data BidiInferenceGrade : Set where
  unresolvedGrade
  approximatelyConstrainedGrade
  exactlyIdentifiedGrade
  : BidiInferenceGrade

approximateNotExact :
  approximatelyConstrainedGrade ≡ exactlyIdentifiedGrade → ⊥
approximateNotExact ()

unresolvedNotExact :
  unresolvedGrade ≡ exactlyIdentifiedGrade → ⊥
unresolvedNotExact ()

ResidualFibre : Set → Set₁
ResidualFibre Hidden = Hidden → Set

FibreRefines : ResidualFibre Hidden → ResidualFibre Hidden → Set
FibreRefines stronger weaker =
  ∀ hidden → stronger hidden → weaker hidden

fibreRefinesRefl :
  (fibre : ResidualFibre Hidden) →
  FibreRefines fibre fibre
fibreRefinesRefl fibre hidden witness = witness

fibreRefinesTrans :
  {stronger middle weaker : ResidualFibre Hidden} →
  FibreRefines stronger middle →
  FibreRefines middle weaker →
  FibreRefines stronger weaker
fibreRefinesTrans strongMiddle middleWeak hidden strong =
  middleWeak hidden (strongMiddle hidden strong)

EvidenceFibre :
  Envelope.Compatible Evidence Hidden →
  Evidence →
  ResidualFibre Hidden
EvidenceFibre compatible evidence hidden = compatible evidence hidden

evidenceRefinementGivesFibreRefinement :
  {compatible : Envelope.Compatible Evidence Hidden}
  {stronger weaker : Evidence} →
  Envelope.EvidenceRefines compatible stronger weaker →
  FibreRefines
    (EvidenceFibre compatible stronger)
    (EvidenceFibre compatible weaker)
evidenceRefinementGivesFibreRefinement refinement hidden strong =
  refinement hidden strong

------------------------------------------------------------------------
-- Measurement backpropagation.
------------------------------------------------------------------------

MeasuredFibre :
  (prior : ResidualFibre Hidden) →
  (measure : Hidden → Measurement) →
  Measurement →
  ResidualFibre Hidden
MeasuredFibre prior measure observed hidden =
  prior hidden × measure hidden ≡ observed

measurementAlwaysRefinesPrior :
  (prior : ResidualFibre Hidden) →
  (measure : Hidden → Measurement) →
  (observed : Measurement) →
  FibreRefines (MeasuredFibre prior measure observed) prior
measurementAlwaysRefinesPrior prior measure observed hidden refined =
  proj₁ refined

TwoMeasurementFibre :
  (prior : ResidualFibre Hidden) →
  (measure₁ : Hidden → Measurement) →
  Measurement →
  (measure₂ : Hidden → Prediction) →
  Prediction →
  ResidualFibre Hidden
TwoMeasurementFibre prior measure₁ observed₁ measure₂ observed₂ hidden =
  prior hidden ×
  (measure₁ hidden ≡ observed₁ × measure₂ hidden ≡ observed₂)

twoMeasurementsRefineFirst :
  (prior : ResidualFibre Hidden) →
  (measure₁ : Hidden → Measurement) →
  (observed₁ : Measurement) →
  (measure₂ : Hidden → Prediction) →
  (observed₂ : Prediction) →
  FibreRefines
    (TwoMeasurementFibre prior measure₁ observed₁ measure₂ observed₂)
    (MeasuredFibre prior measure₁ observed₁)
twoMeasurementsRefineFirst prior measure₁ observed₁ measure₂ observed₂ hidden refined =
  proj₁ refined , proj₁ (proj₂ refined)

PointIdentifies :
  ResidualFibre Hidden →
  (Hidden → Prediction) →
  Set
PointIdentifies fibre consumer =
  ∀ left right →
    fibre left →
    fibre right →
    consumer left ≡ consumer right

record ApproximateResidualReceipt
    (fibre : ResidualFibre Hidden) : Set₁ where
  constructor approximateResidualReceipt
  field
    inferenceGrade : BidiInferenceGrade
    inferenceGradeIsApproximate :
      inferenceGrade ≡ approximatelyConstrainedGrade
    knownConstraintReference : String
    unresolvedResidualReference : String
    provenanceReference : String
    validationReference : String

open ApproximateResidualReceipt public

refinementPreservesApproximateGrade :
  {prior posterior : ResidualFibre Hidden} →
  FibreRefines posterior prior →
  ApproximateResidualReceipt prior →
  String → String → String → String →
  ApproximateResidualReceipt posterior
refinementPreservesApproximateGrade refinement prior known unresolved provenance validation =
  approximateResidualReceipt
    approximatelyConstrainedGrade
    refl
    known
    unresolved
    provenance
    validation

refinementCannotByItselfPromoteToExact :
  {prior posterior : ResidualFibre Hidden} →
  FibreRefines posterior prior →
  approximatelyConstrainedGrade ≡ exactlyIdentifiedGrade →
  ⊥
refinementCannotByItselfPromoteToExact refinement = approximateNotExact

------------------------------------------------------------------------
-- Prediction-envelope bridge.
------------------------------------------------------------------------

record BidiPredictionProblem
    (Evidence Hidden Prediction : Set) : Set₁ where
  constructor bidiPredictionProblem
  field
    compatible : Envelope.Compatible Evidence Hidden
    consumer : Hidden → Prediction
    currentEvidence : Evidence
    evidenceReference : String
    consumerReference : String

open BidiPredictionProblem public

currentResidualFibre :
  BidiPredictionProblem Evidence Hidden Prediction →
  ResidualFibre Hidden
currentResidualFibre problem =
  EvidenceFibre (compatible problem) (currentEvidence problem)

record BidiEvidenceRefinement
    (problem : BidiPredictionProblem Evidence Hidden Prediction)
    (strongerEvidence : Evidence) : Set₁ where
  constructor bidiEvidenceRefinement
  field
    refinesCurrent :
      Envelope.EvidenceRefines
        (compatible problem)
        strongerEvidence
        (currentEvidence problem)
    derivationReference : String
    independentAuthorityReference : String
    residualStillOpenReference : String

open BidiEvidenceRefinement public

bidiEvidenceRefinementShrinksHiddenFibre :
  {problem : BidiPredictionProblem Evidence Hidden Prediction}
  {strongerEvidence : Evidence} →
  BidiEvidenceRefinement problem strongerEvidence →
  FibreRefines
    (EvidenceFibre (compatible problem) strongerEvidence)
    (currentResidualFibre problem)
bidiEvidenceRefinementShrinksHiddenFibre receipt =
  evidenceRefinementGivesFibreRefinement (refinesCurrent receipt)

BidiClosesConsumer :
  BidiPredictionProblem Evidence Hidden Prediction →
  Set
BidiClosesConsumer problem =
  PointIdentifies
    (currentResidualFibre problem)
    (consumer problem)

------------------------------------------------------------------------
-- Residual-obligation bridge.
------------------------------------------------------------------------

record ApproximationWithResidualObligation
    (Exact ResidualPart : Set) : Set where
  constructor approximationWithResidualObligation
  field
    exactOrBoundedPart : Exact
    unresolvedPart : ResidualPart

asExactPlusResidual :
  ∀ {Exact ResidualPart} →
  ApproximationWithResidualObligation Exact ResidualPart →
  Residual.ExactPlusResidual Exact ResidualPart
asExactPlusResidual receipt =
  Residual.exactPlusResidual
    (exactOrBoundedPart receipt)
    (unresolvedPart receipt)

------------------------------------------------------------------------
-- Research-design consequence: useful does not mean closing.
------------------------------------------------------------------------

record PartialInformationExperiment
    (Hidden Measurement : Set) : Set₁ where
  constructor partialInformationExperiment
  field
    prior : ResidualFibre Hidden
    measure : Hidden → Measurement
    expectedOutcomeReference : String
    calibrationReference : String
    expectedResidualReductionReference : String
    exactClosureRequired : Bool
    validationReference : String

open PartialInformationExperiment public

partialMeasurementIsUsefulWithoutExactClosure :
  (experiment : PartialInformationExperiment Hidden Measurement) →
  (observed : Measurement) →
  FibreRefines
    (MeasuredFibre
      (prior experiment)
      (measure experiment)
      observed)
    (prior experiment)
partialMeasurementIsUsefulWithoutExactClosure experiment observed =
  measurementAlwaysRefinesPrior
    (prior experiment)
    (measure experiment)
    observed

record BidiResidualApproximationBoundary : Set where
  constructor bidiResidualApproximationBoundary
  field
    missingExactIdentificationMeansNoInformation : Bool
    missingExactIdentificationMeansNoInformationIsFalse :
      missingExactIdentificationMeansNoInformation ≡ false
    independentlyWarrantedEvidenceCanShrinkResidualFibre : Bool
    independentlyWarrantedEvidenceCanShrinkResidualFibreIsTrue :
      independentlyWarrantedEvidenceCanShrinkResidualFibre ≡ true
    everyUsefulMeasurementMustCloseTheConsumerFibre : Bool
    everyUsefulMeasurementMustCloseTheConsumerFibreIsFalse :
      everyUsefulMeasurementMustCloseTheConsumerFibre ≡ false
    residualRefinementIsMechanismIdentification : Bool
    residualRefinementIsMechanismIdentificationIsFalse :
      residualRefinementIsMechanismIdentification ≡ false
    unresolvedResidualMayBeSilentlyEliminated : Bool
    unresolvedResidualMayBeSilentlyEliminatedIsFalse :
      unresolvedResidualMayBeSilentlyEliminated ≡ false
    repeatedIndependentRefinementsCompose : Bool
    repeatedIndependentRefinementsComposeIsTrue :
      repeatedIndependentRefinementsCompose ≡ true

canonicalBidiResidualApproximationBoundary :
  BidiResidualApproximationBoundary
canonicalBidiResidualApproximationBoundary =
  bidiResidualApproximationBoundary
    false refl
    true refl
    false refl
    false refl
    false refl
    true refl
