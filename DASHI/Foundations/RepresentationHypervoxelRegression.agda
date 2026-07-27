module DASHI.Foundations.RepresentationHypervoxelRegression where

open import DASHI.Core.Prelude

import DASHI.Cognition.SituatedFrameMetacognitionBoundary as Situated
import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Foundations.RepresentationChartInvariant as Representation
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Geometry.RepresentationPrefixUltrametricBridge as Prefix
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SU2SO3

open import DASHI.Foundations.Base369MobiusTransport using
  ( positive
  ; negative
  )

------------------------------------------------------------------------
-- Canonical rank-three Rubik block and one refinement step.
------------------------------------------------------------------------

canonicalRank3Block : Hyper.AxisBlock 3
canonicalRank3Block =
  Hyper.block-cons Hyper.axis-low
    (Hyper.block-cons Hyper.axis-mid
      (Hyper.block-cons Hyper.axis-high Hyper.block-root))

canonicalRank3Root : Hyper.TernaryAddress 3 0
canonicalRank3Root = Hyper.address-root

canonicalRank3Depth1 : Hyper.TernaryAddress 3 1
canonicalRank3Depth1 =
  Hyper.address-refine canonicalRank3Root canonicalRank3Block

canonicalRank3Coarsen :
  Hyper.coarsen canonicalRank3Depth1 ≡ canonicalRank3Root
canonicalRank3Coarsen = refl

canonicalRank3FineBlock :
  Hyper.fineBlock canonicalRank3Depth1 ≡ canonicalRank3Block
canonicalRank3FineBlock = refl

canonicalLiftedRank3Depth1 : Hyper.LiftedAddress 3 1
canonicalLiftedRank3Depth1 =
  Hyper.lifted-address canonicalRank3Depth1 positive

canonicalLiftProjectionInvariant :
  Hyper.projectLiftedAddress
    (Hyper.centralFlip canonicalLiftedRank3Depth1)
  ≡ canonicalRank3Depth1
canonicalLiftProjectionInvariant = refl

------------------------------------------------------------------------
-- Compact regression receipt importing every layer of the tranche.
------------------------------------------------------------------------

record RepresentationHypervoxelRegression : Set₁ where
  field
    ratioThreeSixIsHalf :
      Representation.RatioEquivalent
        Representation.threeSix
        Representation.oneHalf

    decimalPointFiveIsHalf :
      Representation.RatioEquivalent
        Representation.fiveTenths
        Representation.oneHalf

    binaryPointOneIsHalf :
      Representation.RatioEquivalent
        Representation.binaryPointOne
        Representation.oneHalf

    decimalBinaryHalfSameInvariant :
      Representation.RatioEquivalent
        Radix.decimalPointFiveReading
        Radix.binaryPointOneReading

    fiftyPercentIsHalf :
      Representation.RatioEquivalent
        Representation.fiftyHundredths
        Representation.oneHalf

    threeSixIsSecondHarmonic :
      Representation.RatioEquivalent
        Representation.threeSix
        (Representation.harmonicTerm 1)

    threefoldHalfRefinementIsThreeSix :
      Representation.refineRatio 3 Representation.oneHalf
      ≡ Representation.threeSix

    rank1SiteCountIs3 : Hyper.siteCount 1 1 ≡ 3
    rank2SiteCountIs9 : Hyper.siteCount 2 1 ≡ 9
    rank3SiteCountIs27 : Hyper.siteCount 3 1 ≡ 27
    rank3Depth2SiteCountIs729 : Hyper.siteCount 3 2 ≡ 729

    axisLiftCountIs6 : SU2SO3.axisLiftCarrierCount ≡ 6
    operatorSheetCountIs9 : SU2SO3.operatorSheetCount ≡ 9
    liftedSheetCountIs18 : SU2SO3.liftedOperatorSheetCount ≡ 18
    bracketVoxelCountIs27 : SU2SO3.bracketVoxelCount ≡ 27
    liftedBracketVoxelCountIs54 : SU2SO3.liftedBracketVoxelCount ≡ 54
    rank4CountIs81 : SU2SO3.rank4HypervoxelCount ≡ 81
    liftedRank4CountIs162 : SU2SO3.liftedRank4HypervoxelCount ≡ 162

    rankDepthCoarsenLaw :
      Hyper.coarsen canonicalRank3Depth1 ≡ canonicalRank3Root

    liftProjectionLaw :
      Hyper.projectLiftedAddress
        (Hyper.centralFlip canonicalLiftedRank3Depth1)
      ≡ canonicalRank3Depth1

    positiveNegativeParity :
      Hyper.multiplyPolarity positive negative ≡ negative

    negativeNegativeParity :
      Hyper.multiplyPolarity negative negative ≡ positive

    stage1And10Distinct :
      ¬ (Atlas.atlas-1 ≡ Atlas.atlas-10)

    stage10And11Distinct :
      ¬ (Atlas.atlas-10 ≡ Atlas.atlas-11)

    stageCarryJoin : Radix.StageCarryJoin
    decimalCarryGrammar : Radix.CarryGrammar
    p11Projection : Radix.PrimeLaneAddressProjection 3
    prefixUltrametricReceipt : Prefix.OriginPrefixUltrametricReceipt 3

    rightJacobianConvention : SU2SO3.SO3RightJacobianConvention
    haarDensityConvention : SU2SO3.SU2HaarDensityConvention
    quaternionPlaquetteRoute : SU2SO3.QuaternionPlaquetteRoute

    existingLogisticReconciliation :
      Situated.ExistingLogisticCarrierReconciliation

    representationBoundary : Representation.RepresentationAuthorityBoundary
    hypervoxelBoundary : Hyper.HypervoxelAuthorityBoundary
    radixStageBoundary : Radix.RadixStageAuthorityBoundary
    prefixMetricBoundary : Prefix.PrefixMetricAuthorityBoundary
    su2so3Boundary : SU2SO3.SU2SO3369AuthorityBoundary
    situatedFrameBoundary : Situated.SituatedFrameAuthorityBoundary
    primorialBoundary : Situated.PrimorialTransformBoundary

open RepresentationHypervoxelRegression public

canonicalRepresentationHypervoxelRegression :
  RepresentationHypervoxelRegression
canonicalRepresentationHypervoxelRegression = record
  { ratioThreeSixIsHalf = Representation.threeSixIsOneHalf
  ; decimalPointFiveIsHalf = Representation.fiveTenthsIsOneHalf
  ; binaryPointOneIsHalf = Representation.binaryPointOneIsOneHalf
  ; decimalBinaryHalfSameInvariant = Radix.decimalBinaryHalfEquivalent
  ; fiftyPercentIsHalf = Representation.fiftyHundredthsIsOneHalf
  ; threeSixIsSecondHarmonic = Representation.threeSixIsSecondHarmonic
  ; threefoldHalfRefinementIsThreeSix = Representation.threefoldHalfRefinement
  ; rank1SiteCountIs3 = Hyper.rank1Depth1Sites
  ; rank2SiteCountIs9 = Hyper.rank2Depth1Sites
  ; rank3SiteCountIs27 = Hyper.rank3Depth1Sites
  ; rank3Depth2SiteCountIs729 = Hyper.rank3Depth2Sites
  ; axisLiftCountIs6 = SU2SO3.axisLiftCarrierCountIs6
  ; operatorSheetCountIs9 = SU2SO3.operatorSheetCountIs9
  ; liftedSheetCountIs18 = SU2SO3.liftedOperatorSheetCountIs18
  ; bracketVoxelCountIs27 = SU2SO3.bracketVoxelCountIs27
  ; liftedBracketVoxelCountIs54 = SU2SO3.liftedBracketVoxelCountIs54
  ; rank4CountIs81 = SU2SO3.rank4HypervoxelCountIs81
  ; liftedRank4CountIs162 = SU2SO3.liftedRank4HypervoxelCountIs162
  ; rankDepthCoarsenLaw = canonicalRank3Coarsen
  ; liftProjectionLaw = canonicalLiftProjectionInvariant
  ; positiveNegativeParity = refl
  ; negativeNegativeParity = refl
  ; stage1And10Distinct = Radix.stage1NotStage10
  ; stage10And11Distinct = Radix.stage10NotStage11
  ; stageCarryJoin = Radix.canonicalStageCarryJoin
  ; decimalCarryGrammar = Radix.canonicalDecimalCarryGrammar
  ; p11Projection = Radix.canonicalP11ThreeSixNineProjection
  ; prefixUltrametricReceipt = Prefix.canonicalThreeSixPrefixReceipt
  ; rightJacobianConvention = SU2SO3.canonicalSO3RightJacobianConvention
  ; haarDensityConvention = SU2SO3.canonicalSU2HaarDensityConvention
  ; quaternionPlaquetteRoute = SU2SO3.canonicalQuaternionPlaquetteRoute
  ; existingLogisticReconciliation =
      Situated.canonicalExistingLogisticCarrierReconciliation
  ; representationBoundary = Representation.canonicalRepresentationAuthorityBoundary
  ; hypervoxelBoundary = Hyper.canonicalHypervoxelAuthorityBoundary
  ; radixStageBoundary = Radix.canonicalRadixStageAuthorityBoundary
  ; prefixMetricBoundary = Prefix.canonicalPrefixMetricAuthorityBoundary
  ; su2so3Boundary = SU2SO3.canonicalSU2SO3369AuthorityBoundary
  ; situatedFrameBoundary = Situated.canonicalSituatedFrameAuthorityBoundary
  ; primorialBoundary = Situated.canonicalPrimorialTransformBoundary
  }
