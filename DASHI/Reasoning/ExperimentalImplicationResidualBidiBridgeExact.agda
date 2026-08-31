module DASHI.Reasoning.ExperimentalImplicationResidualBidiBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- QUALIFIED IMPLICATION <-> BIDI RESIDUAL FIBRE
--
-- A qualified implication is useful because its downstream quantity/state is
-- constrained but not closed.  This bridge gives that qualification an actual
-- residual fibre which later evidence can refine monotonically.
------------------------------------------------------------------------

record QualifiedImplicationResidual
    {Hidden : Set}
    (edge : Cone.ImplicationEdge) : Set₁ where
  constructor qualifiedImplicationResidual
  field
    edgeIsQualified : Cone.status edge ≡ Cone.qualifiedEdge
    residualFibre : Bidi.ResidualFibre Hidden
    residualReceipt : Bidi.ApproximateResidualReceipt residualFibre
    interpretationReference : String
    closureRequirementReference : String

open QualifiedImplicationResidual public

record RefinedQualifiedImplication
    {Hidden : Set}
    {edge : Cone.ImplicationEdge}
    (prior : QualifiedImplicationResidual {Hidden} edge) : Set₁ where
  constructor refinedQualifiedImplication
  field
    posteriorFibre : Bidi.ResidualFibre Hidden
    posteriorRefinesPrior :
      Bidi.FibreRefines posteriorFibre (residualFibre prior)
    posteriorReceipt : Bidi.ApproximateResidualReceipt posteriorFibre
    newEvidenceReference : String
    remainingResidualReference : String

open RefinedQualifiedImplication public

refinedQualifiedImplicationStillApproximate :
  ∀ {Hidden edge}
    {prior : QualifiedImplicationResidual {Hidden} edge} →
  RefinedQualifiedImplication prior →
  Bidi.BidiInferenceGrade
refinedQualifiedImplicationStillApproximate refined =
  Bidi.inferenceGrade (posteriorReceipt refined)

refinedQualifiedImplicationGradeIsApproximate :
  ∀ {Hidden edge}
    {prior : QualifiedImplicationResidual {Hidden} edge} →
  (refined : RefinedQualifiedImplication prior) →
  Bidi.inferenceGrade (posteriorReceipt refined)
  ≡ Bidi.approximatelyConstrainedGrade
refinedQualifiedImplicationGradeIsApproximate refined =
  Bidi.inferenceGradeIsApproximate (posteriorReceipt refined)

record ImplicationResidualBridgeBoundary : Set where
  constructor implicationResidualBridgeBoundary
  field
    qualifiedEdgeMeansNoInformation : Bool
    qualifiedEdgeMeansNoInformationIsFalse :
      qualifiedEdgeMeansNoInformation ≡ false
    qualifiedEdgeMayCarryRefinableResidualFibre : Bool
    qualifiedEdgeMayCarryRefinableResidualFibreIsTrue :
      qualifiedEdgeMayCarryRefinableResidualFibre ≡ true
    refiningResidualAutomaticallyChangesEdgeToSupported : Bool
    refiningResidualAutomaticallyChangesEdgeToSupportedIsFalse :
      refiningResidualAutomaticallyChangesEdgeToSupported ≡ false

canonicalImplicationResidualBridgeBoundary : ImplicationResidualBridgeBoundary
canonicalImplicationResidualBridgeBoundary =
  implicationResidualBridgeBoundary false refl true refl false refl
