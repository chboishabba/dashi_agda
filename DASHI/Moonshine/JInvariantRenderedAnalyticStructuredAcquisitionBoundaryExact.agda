module DASHI.Moonshine.JInvariantRenderedAnalyticStructuredAcquisitionBoundaryExact where

------------------------------------------------------------------------
-- RENDERED -> ANALYTIC -> STRUCTURED jCOARSE/jFINE ACQUISITION BOUNDARY
--
-- The image/source atlas describes a rendered complex/nome-disk carrier and
-- modular fundamental-domain geometry.  The finite DASHI consumer is the
-- structured jCoarse/jFine state.  These are two separate same-object
-- obligations:
--
--   rendered sample -> analytic modular coordinate
--   analytic modular coordinate -> structured jCoarse/jFine state
--
-- Keeping the split explicit prevents an image classifier from silently
-- acquiring theorem authority over the analytic modular carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.JInvariantImageFractalSourceAtlasExact as Source
import DASHI.Moonshine.JInvariantRiemannObserverResidualSufficiencyBidiExact as Residual
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

record RenderedAnalyticCalibration (Rendered Analytic : Set) : Set₁ where
  field
    calibrate : Rendered → Analytic

open RenderedAnalyticCalibration public

record AnalyticStructuredJAcquisition (Analytic : Set) : Set₁ where
  field
    acquireStructured : Analytic → Residual.StructuredJField

open AnalyticStructuredJAcquisition public

record SameObjectRenderedJAcquisition
    (Rendered Analytic : Set) : Set₁ where
  field
    renderedToAnalytic : RenderedAnalyticCalibration Rendered Analytic
    analyticToStructured : AnalyticStructuredJAcquisition Analytic

open SameObjectRenderedJAcquisition public

acquireRenderedStructured :
  ∀ {Rendered Analytic : Set} →
  SameObjectRenderedJAcquisition Rendered Analytic →
  Rendered → Residual.StructuredJField
acquireRenderedStructured acquisition rendered =
  acquireStructured (analyticToStructured acquisition)
    (calibrate (renderedToAnalytic acquisition) rendered)

structuredToLocal27 : Residual.StructuredJField → Residual.LocalJ27
structuredToLocal27 = Residual.localJObserver

renderedToLocal27 :
  ∀ {Rendered Analytic : Set} →
  SameObjectRenderedJAcquisition Rendered Analytic →
  Rendered → Residual.LocalJ27
renderedToLocal27 acquisition rendered =
  structuredToLocal27 (acquireRenderedStructured acquisition rendered)

------------------------------------------------------------------------
-- Source alignment and theorem boundary.
------------------------------------------------------------------------

sourceDescribesModularFractalCarrier : Bool
sourceDescribesModularFractalCarrier = true

sourceDescribesExceptionalBoundaryGluing : Bool
sourceDescribesExceptionalBoundaryGluing = true

modularFractalSourceDoesNotEntitleKernelProof :
  Source.sourceEntitlesKernelProof Source.modularFractalClaim ≡ false
modularFractalSourceDoesNotEntitleKernelProof = refl

exceptionalGluingSourceDoesNotEntitleKernelProof :
  Source.sourceEntitlesKernelProof Source.exceptionalTriangleGluingClaim ≡ false
exceptionalGluingSourceDoesNotEntitleKernelProof = refl

renderedAcquisitionRelation : Relation.RelationKind
renderedAcquisitionRelation = Relation.exactSameObjectRealisation

renderedAcquisitionHasNoAutomaticTheoremTransfer :
  Relation.TheoremTransferCapability renderedAcquisitionRelation → ⊥
renderedAcquisitionHasNoAutomaticTheoremTransfer =
  Relation.sameObjectAloneCannotDirectlyTransferTheorem

------------------------------------------------------------------------
-- Consumer governance inherited from the RH/j residual BIDI.
------------------------------------------------------------------------

fullStructuredFieldRetainedByDefault : Bool
fullStructuredFieldRetainedByDefault = true

localTwentySevenIsNotGloballyReconstructive : Bool
localTwentySevenIsNotGloballyReconstructive = true

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

data RenderedAnalyticAcquisitionResidual : Set where
  missingRenderedPixelToAnalyticModularCoordinate :
    RenderedAnalyticAcquisitionResidual
  missingAnalyticModularCoordinateToStructuredJField :
    RenderedAnalyticAcquisitionResidual
  missingStructuredJFieldToOrbitIndexRecognizer :
    RenderedAnalyticAcquisitionResidual
  missingAnalyticFrickeFiniteTransportIntertwiner :
    RenderedAnalyticAcquisitionResidual

record RenderedAnalyticAcquisitionFrontier : Set where
  constructor rendered-analytic-acquisition-frontier
  field
    sourceDescribesRenderedAnalyticCarrier : Bool
    twoStageAcquisitionTyped : Bool
    localTwentySevenKeptDownstreamOfFullField : Bool
    sourceClaimAutomaticallyPaysCalibration : Bool
    sourceClaimAutomaticallyPaysStructuredLift : Bool
    renderedCalibrationConstructed : Bool
    analyticStructuredLiftConstructed : Bool
    firstResidual : RenderedAnalyticAcquisitionResidual

canonicalRenderedAnalyticAcquisitionFrontier :
  RenderedAnalyticAcquisitionFrontier
canonicalRenderedAnalyticAcquisitionFrontier =
  rendered-analytic-acquisition-frontier
    true true true false false false false
    missingRenderedPixelToAnalyticModularCoordinate
