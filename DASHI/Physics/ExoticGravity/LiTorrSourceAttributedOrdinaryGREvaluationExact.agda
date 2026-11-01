module DASHI.Physics.ExoticGravity.LiTorrSourceAttributedOrdinaryGREvaluationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact as Theory
import DASHI.Physics.ExoticGravity.LiTorrSIOrdinaryGRComparatorHandoffExact as Handoff
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact as GRCompile

------------------------------------------------------------------------
-- SOURCE-ATTRIBUTED ORDINARY-GR EVALUATION
--
-- Every input remains bound to its epistemic role.  Amy-attributed statements,
-- historical theory papers, modern DASHI reconstructions, and apparatus
-- measurements are not interchangeable receipts.
------------------------------------------------------------------------

data SourceRole : Set where
  amyAttributedStatement : SourceRole
  primaryTheoryPaper : SourceRole
  modernDASHIReconstruction : SourceRole
  experimentalMeasurement : SourceRole
  institutionalRecord : SourceRole

data EntitlementLevel : Set where
  bibliographicIdentityOnly : EntitlementLevel
  inspectedCarrier : EntitlementLevel
  exactLocatedStatement : EntitlementLevel
  sameApparatusMeasurement : EntitlementLevel

record RoleBoundSource : Set where
  constructor role-bound-source
  field
    source : Attribution.AttributedSource
    role : SourceRole
    entitlement : EntitlementLevel
    exactLocator : String
    claimScope : String

open RoleBoundSource public

record SourceAttributedOrdinaryGREvaluationInput : Set₂ where
  constructor source-attributed-ordinary-gr-evaluation-input
  field
    handoff : Handoff.SIOrdinaryGRHandoffInput
    theorySource : RoleBoundSource
    theorySourceRoleIsPrimaryTheory : role theorySource ≡ primaryTheoryPaper
    reconstructionSource : RoleBoundSource
    reconstructionRoleIsDASHI : role reconstructionSource ≡ modernDASHIReconstruction
    apparatusMeasurementSource : RoleBoundSource
    apparatusSourceRoleIsMeasurement : role apparatusMeasurementSource ≡ experimentalMeasurement
    apparatusSourceIsSameApparatus : entitlement apparatusMeasurementSource ≡ sameApparatusMeasurement
    sourceRolesKeptDistinct : Bool

open SourceAttributedOrdinaryGREvaluationInput public

compileAttributedOrdinaryGRRequest :
  SourceAttributedOrdinaryGREvaluationInput →
  GRCompile.OrdinaryGREvaluationRequest
compileAttributedOrdinaryGRRequest input =
  Handoff.compileSIOrdinaryGRRequest
    (SourceAttributedOrdinaryGREvaluationInput.handoff input)

record SourceAttributedNumericalPrediction : Set₂ where
  constructor source-attributed-numerical-prediction
  field
    input : SourceAttributedOrdinaryGREvaluationInput
    request : GRCompile.OrdinaryGREvaluationRequest
    predictionCarrier : String
    evaluatorIdentity : String
    evaluatorRevision : String
    NumericalEvaluationReceipt : Set
    numericalEvaluationReceipt : NumericalEvaluationReceipt
    SameInputPredictionReceipt : Set
    sameInputPredictionReceipt : SameInputPredictionReceipt
    numericalMethodSource : RoleBoundSource
    methodRoleIsDASHIReconstruction :
      role numericalMethodSource ≡ modernDASHIReconstruction

open SourceAttributedNumericalPrediction public

------------------------------------------------------------------------
-- Theory-source diligence cross-check.
--
-- Bibliographic identity for the Li/Torr papers is useful provenance, but the
-- existing diligence owner still keeps inspected-carrier and exact-locator
-- residuals open where applicable.  This owner does not silently upgrade them.
------------------------------------------------------------------------

prd1991StillNeedsCarrierAndLocator : Bool
prd1991StillNeedsCarrierAndLocator = true

prb1992StillNeedsCarrierAndLocator : Bool
prb1992StillNeedsCarrierAndLocator = true

fopl1993StillNeedsCarrierAndLocator : Bool
fopl1993StillNeedsCarrierAndLocator = true

record AttributionPromotionBoundary : Set where
  constructor attribution-promotion-boundary
  field
    amyStatementMayPayPrimaryTheoryEquation : Bool
    primaryTheoryPaperMayPayApparatusMeasurement : Bool
    dashiReconstructionMayBeAttributedToAmy : Bool
    bibliographicIdentityMayPayExactEquationLocator : Bool
    experimentalMeasurementMayBeAttributedToHistoricalAuthor : Bool
    sameObjectMeasurementRequiredForNumericalComparison : Bool
    exactSourceRoleMustSurviveToPrediction : Bool
    citationImportsScientificProof : Bool

canonicalAttributionPromotionBoundary : AttributionPromotionBoundary
canonicalAttributionPromotionBoundary =
  attribution-promotion-boundary
    false false false false false true true false
