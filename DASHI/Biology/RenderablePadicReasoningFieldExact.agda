module DASHI.Biology.RenderablePadicReasoningFieldExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Biology.PadicCylinderLODReasoningField as LOD
import DASHI.Biology.HybridPadicReasoningFieldBridgeExact as Hybrid
import DASHI.Biology.ReasoningFieldRenderBridgeExact as ExistingRender

------------------------------------------------------------------------
-- Supplied sections 801--835.  The exact state is a finite ternary prefix or a
-- hybrid prefix/chart state.  Euclidean voxels, colours, opacity, and camera
-- pixels are observation carriers with explicit information loss.

------------------------------------------------------------------------
-- Project address syntax is separate from canonical ternary digits and from
-- ordinary decimal notation.

data ProjectGlyph : Set where
  glyph3 : ProjectGlyph
  glyph6 : ProjectGlyph
  glyph9 : ProjectGlyph

record ProjectAddress3 : Set where
  constructor projectAddress3
  field
    glyphOne : ProjectGlyph
    glyphTwo : ProjectGlyph
    glyphThree : ProjectGlyph

open ProjectAddress3 public

canonicalProjectAddress : ProjectAddress3
canonicalProjectAddress = projectAddress3 glyph3 glyph9 glyph3

glyphToTernaryDigit : ProjectGlyph → U369.Digit369
glyphToTernaryDigit glyph3 = U369.digit3
glyphToTernaryDigit glyph6 = U369.digit6
glyphToTernaryDigit glyph9 = U369.digit9

projectAddressToPrefix : ProjectAddress3 → LOD.DepthThreeAddress
projectAddressToPrefix (projectAddress3 a b c) =
  glyphToTernaryDigit a vcons
  glyphToTernaryDigit b vcons
  glyphToTernaryDigit c vcons
  vnil

projectAddressConversionWitness :
  projectAddressToPrefix canonicalProjectAddress
  ≡
  U369.digit3 vcons U369.digit9 vcons U369.digit3 vcons vnil
projectAddressConversionWitness = refl

data AddressInterpretation : Set where
  symbolicProjectPath : AddressInterpretation
  ordinaryDecimalNumber : AddressInterpretation
  canonicalThreeAdicPrefix : AddressInterpretation

------------------------------------------------------------------------
-- Prefix truncation is an exact quotient projection but not an inverse for the
-- discarded child digit.

sameParentChild3 : LOD.DepthTwoAddress
sameParentChild3 =
  LOD.refineOne (U369.digit6 vcons vnil) U369.digit3

sameParentChild9 : LOD.DepthTwoAddress
sameParentChild9 =
  LOD.refineOne (U369.digit6 vcons vnil) U369.digit9

childrenShareQuotient :
  LOD.prefixTwoToOne sameParentChild3
  ≡
  LOD.prefixTwoToOne sameParentChild9
childrenShareQuotient = refl

childrenRemainDistinct : sameParentChild3 ≡ sameParentChild9 → ⊥
childrenRemainDistinct ()

------------------------------------------------------------------------
-- Finite ultrametric fields are locally constant on cylinders once the kernel
-- depends only on a resolved prefix.

prefixTwoCode : LOD.DepthThreeAddress → Nat
prefixTwoCode
  (U369.digit3 vcons U369.digit3 vcons c vcons vnil) = 0
prefixTwoCode
  (U369.digit3 vcons U369.digit6 vcons c vcons vnil) = 1
prefixTwoCode
  (U369.digit3 vcons U369.digit9 vcons c vcons vnil) = 2
prefixTwoCode
  (U369.digit6 vcons U369.digit3 vcons c vcons vnil) = 3
prefixTwoCode
  (U369.digit6 vcons U369.digit6 vcons c vcons vnil) = 4
prefixTwoCode
  (U369.digit6 vcons U369.digit9 vcons c vcons vnil) = 5
prefixTwoCode
  (U369.digit9 vcons U369.digit3 vcons c vcons vnil) = 6
prefixTwoCode
  (U369.digit9 vcons U369.digit6 vcons c vcons vnil) = 7
prefixTwoCode
  (U369.digit9 vcons U369.digit9 vcons c vcons vnil) = 8

prefixKernel : LOD.DepthThreeAddress → Nat
prefixKernel address = suc (prefixTwoCode address)

localCylinderPointA : LOD.DepthThreeAddress
localCylinderPointA =
  U369.digit3 vcons U369.digit6 vcons U369.digit3 vcons vnil

localCylinderPointB : LOD.DepthThreeAddress
localCylinderPointB =
  U369.digit3 vcons U369.digit6 vcons U369.digit9 vcons vnil

kernelLocallyConstantOnDepthTwoCylinder :
  prefixKernel localCylinderPointA
  ≡
  prefixKernel localCylinderPointB
kernelLocallyConstantOnDepthTwoCylinder = refl

------------------------------------------------------------------------
-- Intrinsic ternary self-similarity and Euclidean observation geometry are
-- represented separately.

data IntrinsicGeometry : Set where
  prefixUltrametric : IntrinsicGeometry
  threeAdicCompletionGeometry : IntrinsicGeometry

data EuclideanObservationGeometry : Set where
  mortonInterleavingLayout : EuclideanObservationGeometry
  coordinatewiseThreeAxisLayout : EuclideanObservationGeometry
  customLearnedLayout : EuclideanObservationGeometry

data ExpansionPolicy : Set where
  retainOriginalAddress : ExpansionPolicy
  halfOpenCellConvention : ExpansionPolicy
  nonEventuallyTwoConvention : ExpansionPolicy

canonicalExpansionPolicy : ExpansionPolicy
canonicalExpansionPolicy = retainOriginalAddress

------------------------------------------------------------------------
-- Correct finite depth counts and Morton-like interleaving.  The depth-six
-- implementation is reused; depth nine consumes three digits per display axis.

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

depthSixPrefixCount : Nat
depthSixPrefixCount = pow3 6

depthNinePrefixCount : Nat
depthNinePrefixCount = pow3 9

depthSixCountIs729 : depthSixPrefixCount ≡ 729
depthSixCountIs729 = refl

depthNineCountIs19683 : depthNinePrefixCount ≡ 19683
depthNineCountIs19683 = refl

depthSixCubeSide : Nat
depthSixCubeSide = pow3 2

depthNineCubeSide : Nat
depthNineCubeSide = pow3 3

depthSixCubeCloses :
  depthSixCubeSide * depthSixCubeSide * depthSixCubeSide
  ≡
  depthSixPrefixCount
depthSixCubeCloses = refl

depthNineCubeCloses :
  depthNineCubeSide * depthNineCubeSide * depthNineCubeSide
  ≡
  depthNinePrefixCount
depthNineCubeCloses = refl

DepthNineAddress : Set
DepthNineAddress = U369.Address 9

ternaryCoordinate3 :
  U369.Digit369 → U369.Digit369 → U369.Digit369 → Nat
ternaryCoordinate3 high middle low =
  9 * LOD.digitCoordinate high
  + 3 * LOD.digitCoordinate middle
  + LOD.digitCoordinate low

embedDepthNine : DepthNineAddress → LOD.Voxel3
embedDepthNine
  (a0 vcons a1 vcons a2 vcons
   a3 vcons a4 vcons a5 vcons
   a6 vcons a7 vcons a8 vcons vnil) =
  LOD.voxel3
    (ternaryCoordinate3 a0 a3 a6)
    (ternaryCoordinate3 a1 a4 a7)
    (ternaryCoordinate3 a2 a5 a8)

sampleDepthNine : DepthNineAddress
sampleDepthNine =
  U369.digit6 vcons U369.digit9 vcons U369.digit3 vcons
  U369.digit9 vcons U369.digit6 vcons U369.digit3 vcons
  U369.digit3 vcons U369.digit9 vcons U369.digit6 vcons
  vnil

sampleDepthNineVoxel :
  embedDepthNine sampleDepthNine ≡ LOD.voxel3 15 23 1
sampleDepthNineVoxel = refl

------------------------------------------------------------------------
-- LOD is retained digit depth.  Parent mass and class masses are aggregated
-- before normalised class weights are computed.

data LODDepth : Set where
  depthOne : LODDepth
  depthTwo : LODDepth
  depthThree : LODDepth
  depthSix : LODDepth
  depthNine : LODDepth

parentMassConsistency :
  LOD.aggregateNat LOD.canonicalChildMasses ≡ 9
parentMassConsistency = LOD.canonicalParentMassIsNine

parentAverageConsistency :
  3 * LOD.parentValue LOD.canonicalAverageCertificate
  ≡
  LOD.aggregateNat
    (LOD.childValues LOD.canonicalAverageCertificate)
parentAverageConsistency =
  LOD.threeTimesParentIsChildSum LOD.canonicalAverageCertificate

record RationalWeight : Set where
  constructor rationalWeight
  field
    weightNumerator : Nat
    weightDenominator : Nat

open RationalWeight public

naiveAverageOfChildWeights : RationalWeight
naiveAverageOfChildWeights = rationalWeight 1 2

weightAfterMassAggregation : RationalWeight
weightAfterMassAggregation = rationalWeight 1 10

normaliseAfterAggregationMatters :
  naiveAverageOfChildWeights ≡ weightAfterMassAggregation → ⊥
normaliseAfterAggregationMatters ()

------------------------------------------------------------------------
-- Adaptive refinement and sparse prefix trees.

data VariationBand : Set where
  lowVariation : VariationBand
  highVariation : VariationBand

data RefinementDecision : Set where
  retainParent : RefinementDecision
  refineChildren : RefinementDecision

refinementDecision : VariationBand → RefinementDecision
refinementDecision lowVariation = retainParent
refinementDecision highVariation = refineChildren

canonicalVariationMagnitude :
  LOD.childVariation (LOD.threeChildren 1 5 9) ≡ 8
canonicalVariationMagnitude = refl

canonicalHighVariationRefines :
  refinementDecision highVariation ≡ refineChildren
canonicalHighVariationRefines = refl

record SparsePrefixNode : Set where
  constructor sparsePrefixNode
  field
    nodeDepth : LODDepth
    nodeMass : Nat
    nodeVariation : Nat
    nodeRetained : Bool

open SparsePrefixNode public

canonicalSparseNode : SparsePrefixNode
canonicalSparseNode = sparsePrefixNode depthThree 9 8 true

sparseNodeRetained : nodeRetained canonicalSparseNode ≡ true
sparseNodeRetained = refl

------------------------------------------------------------------------
-- Rendering choices.  Per-voxel self-normalisation destroys contrast; shared
-- calibration preserves it.  Compositing semantics remain explicit.

data PositiveDensity : Set where
  lowPositiveDensity : PositiveDensity
  highPositiveDensity : PositiveDensity

badPerVoxelOpacity : PositiveDensity → Nat
badPerVoxelOpacity lowPositiveDensity = 1
badPerVoxelOpacity highPositiveDensity = 1

sharedOpacity : PositiveDensity → Nat
sharedOpacity lowPositiveDensity = 2
sharedOpacity highPositiveDensity = 8

perVoxelNormalisationErasesContrast :
  badPerVoxelOpacity lowPositiveDensity
  ≡
  badPerVoxelOpacity highPositiveDensity
perVoxelNormalisationErasesContrast = refl

sharedCalibrationRetainsContrast :
  sharedOpacity lowPositiveDensity
  ≡
  sharedOpacity highPositiveDensity
  →
  ⊥
sharedCalibrationRetainsContrast ()

data VolumeRenderingMode : Set where
  maximumIntensityProjection : VolumeRenderingMode
  straightAlphaCompositing : VolumeRenderingMode
  additiveEmission : VolumeRenderingMode
  isosurfaceRendering : VolumeRenderingMode

renderTwoSamples : VolumeRenderingMode → Nat → Nat → Nat
renderTwoSamples maximumIntensityProjection left right = left ⊔ right
renderTwoSamples straightAlphaCompositing left right = left + right ∸ 1
renderTwoSamples additiveEmission left right = left + right
renderTwoSamples isosurfaceRendering left right = 1

renderModesHaveDifferentSemantics :
  renderTwoSamples maximumIntensityProjection 3 4
  ≡
  renderTwoSamples additiveEmission 3 4
  →
  ⊥
renderModesHaveDifferentSemantics ()

data PrefixCellPolicy : Set where
  pointSplatOnly : PrefixCellPolicy
  fullPrefixCell : PrefixCellPolicy
  directRayAddressEvaluation : PrefixCellPolicy

------------------------------------------------------------------------
-- Prefix caching and exact address retention reuse the existing renderer.

prefixCacheReuse :
  LOD.coarseVoxel (LOD.embedDepthSix ExistingRender.sameCoarseAddressA)
  ≡
  LOD.coarseVoxel (LOD.embedDepthSix ExistingRender.sameCoarseAddressB)
prefixCacheReuse = ExistingRender.coarseVoxelCacheKeyAgrees

fineAddressesStillDiffer :
  LOD.fineVoxel (LOD.embedDepthSix ExistingRender.sameCoarseAddressA)
  ≡
  LOD.voxel3 0 0 0
  ×
  LOD.fineVoxel (LOD.embedDepthSix ExistingRender.sameCoarseAddressB)
  ≡
  LOD.voxel3 2 2 2
fineAddressesStillDiffer = ExistingRender.fineVoxelStillDiffers

------------------------------------------------------------------------
-- Discrete hierarchy and continuous local charts form a product carrier.  A
-- finite difference is a declared scale probe, not automatically a derivative.

data StateCarrier : Set where
  purePrefixCarrier : StateCarrier
  hybridPrefixChartCarrier : StateCarrier

data DifferenceScale : Set where
  coarseDifference : DifferenceScale
  fineDifference : DifferenceScale

fieldAtScale : DifferenceScale → Nat
fieldAtScale coarseDifference = 3
fieldAtScale fineDifference = 8

hierarchicalFiniteDifference : DifferenceScale → Nat
hierarchicalFiniteDifference coarseDifference = 0
hierarchicalFiniteDifference fineDifference = 5

fineScaleRevealsChange :
  hierarchicalFiniteDifference fineDifference ≡ 5
fineScaleRevealsChange = refl

hybridBridgeRetainsSeparateCoordinates :
  Hybrid.combinedAddressRetainsBothCoordinateKinds
    Hybrid.canonicalHybridPadicReasoningBoundary
  ≡
  true
hybridBridgeRetainsSeparateCoordinates =
  Hybrid.combinedAddressRetainsBothCoordinateKindsIsTrue
    Hybrid.canonicalHybridPadicReasoningBoundary

------------------------------------------------------------------------
-- Finished renderable object and authority boundaries.

record RenderableReasoningField : Set where
  constructor renderableReasoningField
  field
    stateCarrier : StateCarrier
    measureDeclared : Bool
    totalActivityDeclared : Bool
    classFieldDeclared : Bool
    quotientDepth : LODDepth
    observationGeometry : EuclideanObservationGeometry
    colourMapDeclared : Bool
    opacityMapDeclared : Bool
    addressMetadataRetained : Bool

open RenderableReasoningField public

canonicalRenderableReasoningField : RenderableReasoningField
canonicalRenderableReasoningField =
  renderableReasoningField
    hybridPrefixChartCarrier
    true
    true
    true
    depthSix
    mortonInterleavingLayout
    true
    true
    true

canonicalFieldRetainsAddress :
  addressMetadataRetained canonicalRenderableReasoningField ≡ true
canonicalFieldRetainsAddress = refl

record RenderablePadicReasoningBoundary : Set where
  constructor renderablePadicReasoningBoundary
  field
    projectDecimalSyntaxIsCanonicalThreeAdicNotation : Bool
    projectDecimalSyntaxIsCanonicalThreeAdicNotationIsFalse :
      projectDecimalSyntaxIsCanonicalThreeAdicNotation ≡ false

    truncationIsGloballyLossless : Bool
    truncationIsGloballyLosslessIsFalse :
      truncationIsGloballyLossless ≡ false

    euclideanEmbeddingIsCanonicalIsometry : Bool
    euclideanEmbeddingIsCanonicalIsometryIsFalse :
      euclideanEmbeddingIsCanonicalIsometry ≡ false

    intrinsicThreeAdicSelfSimilarityFixesVisibleFractal : Bool
    intrinsicThreeAdicSelfSimilarityFixesVisibleFractalIsFalse :
      intrinsicThreeAdicSelfSimilarityFixesVisibleFractal ≡ false

    inverseFloatingPointCoordinateHasUniqueAddress : Bool
    inverseFloatingPointCoordinateHasUniqueAddressIsFalse :
      inverseFloatingPointCoordinateHasUniqueAddress ≡ false

    perVoxelSelfNormalisationPreservesDensityContrast : Bool
    perVoxelSelfNormalisationPreservesDensityContrastIsFalse :
      perVoxelSelfNormalisationPreservesDensityContrast ≡ false

    finiteDifferenceIsAutomaticallyThreeAdicDerivative : Bool
    finiteDifferenceIsAutomaticallyThreeAdicDerivativeIsFalse :
      finiteDifferenceIsAutomaticallyThreeAdicDerivative ≡ false

    finalImageIsPrimaryReasoningState : Bool
    finalImageIsPrimaryReasoningStateIsFalse :
      finalImageIsPrimaryReasoningState ≡ false

open RenderablePadicReasoningBoundary public

canonicalRenderablePadicReasoningBoundary :
  RenderablePadicReasoningBoundary
canonicalRenderablePadicReasoningBoundary =
  renderablePadicReasoningBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
