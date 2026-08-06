module DASHI.Visualisation.SelfConsistentEventRendererExact where

open import DASHI.Core.Prelude

import DASHI.Visualisation.EventFilamentFieldExact as Event
import DASHI.Visualisation.RendererParityExact as CMYK

------------------------------------------------------------------------
-- Finite exact renderer spine for supplied sections 710--755.  It separates
-- frame action, Euclidean and ultrametric affinity, positive kernels, density
-- feedback, ambiguity attenuation, class semantics, colour, and observation.

data FrameConvention : Set where
  activeEventMotion : FrameConvention
  passiveFrameMotion : FrameConvention

record FramedCoordinate : Set where
  constructor framedCoordinate
  field
    frameX : Nat
    frameY : Nat

open FramedCoordinate public

applyFrame : FrameConvention → Nat → Nat → FramedCoordinate
applyFrame activeEventMotion x shift = framedCoordinate (x + shift) 0
applyFrame passiveFrameMotion x shift = framedCoordinate (x ∸ shift) 0

activeAndPassiveDiffer :
  applyFrame activeEventMotion 3 1
  ≡
  applyFrame passiveFrameMotion 3 1
  →
  ⊥
activeAndPassiveDiffer ()

------------------------------------------------------------------------
-- Query points require a separately declared hierarchical address.  Shared
-- depth and p-adic distance are not inferred from Euclidean coordinates.

data AddressDigit : Set where
  address0 : AddressDigit
  address1 : AddressDigit
  address2 : AddressDigit

record Address3 : Set where
  constructor address3
  field
    prefix0 : AddressDigit
    prefix1 : AddressDigit
    prefix2 : AddressDigit

open Address3 public

record QueryPoint : Set where
  constructor queryPoint
  field
    continuousX : Nat
    continuousY : Nat
    hierarchyAddress : Address3

open QueryPoint public

canonicalQuery : QueryPoint
canonicalQuery =
  queryPoint 2 4 (address3 address1 address2 address0)

queryAddressIsAdditionalStructure :
  hierarchyAddress canonicalQuery ≡ address3 address1 address2 address0
queryAddressIsAdditionalStructure = refl

data SharedDepth : Set where
  shared0 : SharedDepth
  shared1 : SharedDepth
  shared2 : SharedDepth
  shared3 : SharedDepth

sharedDepthWeight : SharedDepth → Nat
sharedDepthWeight shared0 = 1
sharedDepthWeight shared1 = 2
sharedDepthWeight shared2 = 3
sharedDepthWeight shared3 = 4

closerBranchGetsLargerWeight :
  sharedDepthWeight shared0 ≡ 1
  ×
  sharedDepthWeight shared3 ≡ 4
closerBranchGetsLargerWeight = refl , refl

legacyDecreasingWeight : SharedDepth → Nat
legacyDecreasingWeight shared0 = 4
legacyDecreasingWeight shared1 = 3
legacyDecreasingWeight shared2 = 2
legacyDecreasingWeight shared3 = 1

legacyWeightHasWrongDirection :
  legacyDecreasingWeight shared0 ≡ 4
  ×
  legacyDecreasingWeight shared3 ≡ 1
legacyWeightHasWrongDirection = refl , refl

combinedAffinity : Nat → SharedDepth → Nat
combinedAffinity euclideanKernel depth =
  euclideanKernel * sharedDepthWeight depth

canonicalProductAffinity : combinedAffinity 3 shared2 ≡ 9
canonicalProductAffinity = refl

additiveAffinity : Nat → SharedDepth → Nat
additiveAffinity euclideanKernel depth =
  euclideanKernel + sharedDepthWeight depth

productAndAdditiveAreModellingChoices :
  combinedAffinity 3 shared2 ≡ additiveAffinity 3 shared2 → ⊥
productAndAdditiveAreModellingChoices ()

------------------------------------------------------------------------
-- Positive kernel wrapper and base pass.

data SignedActivation : Set where
  activationNegative : SignedActivation
  activationZero : SignedActivation
  activationPositive : SignedActivation

positiveActivation : SignedActivation → Nat
positiveActivation activationNegative = 0
positiveActivation activationZero = 0
positiveActivation activationPositive = 3

record BaseEventContribution : Set where
  constructor baseEventContribution
  field
    eventWeight : Nat
    hierarchyWeight : Nat
    kernelValue : Nat
    classWeights : Event.ClassMass3

open BaseEventContribution public

baseContributionMass : BaseEventContribution → Nat
baseContributionMass contribution =
  eventWeight contribution
  * hierarchyWeight contribution
  * kernelValue contribution

canonicalBaseContribution : BaseEventContribution
canonicalBaseContribution =
  baseEventContribution 2 3 1 (Event.classMass3 2 1 1)

canonicalBaseMassIsSix :
  baseContributionMass canonicalBaseContribution ≡ 6
canonicalBaseMassIsSix = refl

------------------------------------------------------------------------
-- Two-pass density-dependent sharpness.  The finite coefficient is bounded by
-- construction, and the explicit second pass breaks the circular dependency.

data DensityBand : Set where
  sparseBand : DensityBand
  mediumBand : DensityBand
  denseBand : DensityBand

baseSharpness : Nat
baseSharpness = 1

minimumSharpness : Nat
minimumSharpness = 1

maximumSharpness : Nat
maximumSharpness = 3

effectiveSharpness : DensityBand → Nat
effectiveSharpness sparseBand = minimumSharpness
effectiveSharpness mediumBand = 2
effectiveSharpness denseBand = maximumSharpness

sharpnessRemainsInDeclaredRange :
  effectiveSharpness sparseBand ≡ 1
  ×
  effectiveSharpness mediumBand ≡ 2
  ×
  effectiveSharpness denseBand ≡ 3
sharpnessRemainsInDeclaredRange = refl , (refl , refl)

baseField : DensityBand → Nat
baseField sparseBand = 2
baseField mediumBand = 5
baseField denseBand = 8

secondPassField : DensityBand → Nat
secondPassField band =
  baseField band * effectiveSharpness band

canonicalTwoPassDenseField : secondPassField denseBand ≡ 24
canonicalTwoPassDenseField = refl

------------------------------------------------------------------------
-- A complete finite fixed-point model.  It proves existence, uniqueness, and
-- convergence for this declared operator without promoting the result to the
-- continuum renderer before a contraction estimate is supplied.

data DensityState : Set where
  densitySeed : DensityState
  densityIntermediate : DensityState
  densityFixed : DensityState

fieldOperator : DensityState → DensityState
fieldOperator densitySeed = densityIntermediate
fieldOperator densityIntermediate = densityFixed
fieldOperator densityFixed = densityFixed

iterateTwo : DensityState → DensityState
iterateTwo state = fieldOperator (fieldOperator state)

seedConvergesInTwoSteps : iterateTwo densitySeed ≡ densityFixed
seedConvergesInTwoSteps = refl

fixedStateIsFixed : fieldOperator densityFixed ≡ densityFixed
fixedStateIsFixed = refl

fixedPointUnique :
  (state : DensityState) →
  fieldOperator state ≡ state →
  state ≡ densityFixed
fixedPointUnique densitySeed ()
fixedPointUnique densityIntermediate ()
fixedPointUnique densityFixed refl = refl

record FixedPointReceipt : Set where
  constructor fixedPointReceipt
  field
    dampingNumerator : Nat
    dampingDenominator : Nat
    toleranceScaled : Nat
    maximumIterations : Nat
    iterationsUsed : Nat
    converged : Bool

open FixedPointReceipt public

canonicalFixedPointReceipt : FixedPointReceipt
canonicalFixedPointReceipt = fixedPointReceipt 1 2 1 8 2 true

fixedPointReceiptConverged :
  converged canonicalFixedPointReceipt ≡ true
fixedPointReceiptConverged = refl

------------------------------------------------------------------------
-- Pointwise and event-centre feedback are different kernel semantics.

data FeedbackScope : Set where
  pointwiseFeedback : FeedbackScope
  eventCentreFeedback : FeedbackScope

feedbackSharpness : FeedbackScope → Nat → Nat
feedbackSharpness pointwiseFeedback localDensity = suc localDensity
feedbackSharpness eventCentreFeedback centreDensity = 2 * centreDensity

feedbackScopesDiffer :
  feedbackSharpness pointwiseFeedback 2
  ≡
  feedbackSharpness eventCentreFeedback 2
  →
  ⊥
feedbackScopesDiffer ()

------------------------------------------------------------------------
-- Ambiguity attenuation.  The legacy signed term amplifies a positive gap;
-- the corrected positive function suppresses ties and tends to one as the gap
-- grows in this finite table.

data TopTwoGap : Set where
  tiedTopTwo : TopTwoGap
  smallTopTwoGap : TopTwoGap
  largeTopTwoGap : TopTwoGap

data VisibilityEffect : Set where
  attenuatedVisibility : VisibilityEffect
  unchangedVisibility : VisibilityEffect
  amplifiedVisibility : VisibilityEffect

legacyTieEffect : TopTwoGap → VisibilityEffect
legacyTieEffect tiedTopTwo = attenuatedVisibility
legacyTieEffect smallTopTwoGap = amplifiedVisibility
legacyTieEffect largeTopTwoGap = amplifiedVisibility

correctedTieFactor : TopTwoGap → Nat
correctedTieFactor tiedTopTwo = 1
correctedTieFactor smallTopTwoGap = 2
correctedTieFactor largeTopTwoGap = 3

legacyPositiveGapAmplifies :
  legacyTieEffect smallTopTwoGap ≡ amplifiedVisibility
legacyPositiveGapAmplifies = refl

correctedTieSuppressionTable :
  correctedTieFactor tiedTopTwo ≡ 1
  ×
  correctedTieFactor largeTopTwoGap ≡ 3
correctedTieSuppressionTable = refl , refl

record ClassProfile : Set where
  constructor classProfile
  field
    profileA : Nat
    profileB : Nat
    profileC : Nat
    profileScale : Nat

open ClassProfile public

baseProfile : ClassProfile
baseProfile = classProfile 2 1 1 4

uniformlyAttenuatedProfile : ClassProfile
uniformlyAttenuatedProfile = classProfile 2 1 1 4

classSpecificProfile : ClassProfile
classSpecificProfile = classProfile 1 2 1 4

uniformAttenuationCancelsFromComposition :
  baseProfile ≡ uniformlyAttenuatedProfile
uniformAttenuationCancelsFromComposition = refl

classSpecificAttenuationChangesComposition :
  baseProfile ≡ classSpecificProfile → ⊥
classSpecificAttenuationChangesComposition ()

------------------------------------------------------------------------
-- Exact composition versus epsilon/void conventions.

record NormalisationWithVoid : Set where
  constructor normalisationWithVoid
  field
    visibleMass : Nat
    voidMass : Nat
    denominator : Nat
    closesWithVoid : visibleMass + voidMass ≡ denominator

open NormalisationWithVoid public

canonicalVoidNormalisation : NormalisationWithVoid
canonicalVoidNormalisation = normalisationWithVoid 7 3 10 refl

voidChannelClosesDenominator :
  visibleMass canonicalVoidNormalisation
  + voidMass canonicalVoidNormalisation
  ≡ denominator canonicalVoidNormalisation
voidChannelClosesDenominator = closesWithVoid canonicalVoidNormalisation

------------------------------------------------------------------------
-- Frame-relative maximum normalisation is distinct from fixed calibration.

data CalibrationMode : Set where
  frameMaximumCalibration : CalibrationMode
  fixedReferenceCalibration : CalibrationMode
  robustQuantileCalibration : CalibrationMode

calibratedDensity : CalibrationMode → Nat → Nat
calibratedDensity frameMaximumCalibration raw = raw ∸ 1
calibratedDensity fixedReferenceCalibration raw = raw
calibratedDensity robustQuantileCalibration raw = raw + 1

calibrationChangesDisplayedDensity :
  calibratedDensity frameMaximumCalibration 4
  ≡
  calibratedDensity fixedReferenceCalibration 4
  →
  ⊥
calibrationChangesDisplayedDensity ()

------------------------------------------------------------------------
-- Opacity and inverse luminance have opposite observation semantics.

threadOpacity : Nat → Nat
threadOpacity density = density

inverseVoidLuminance : Nat → Nat
inverseVoidLuminance density = 10 ∸ density

highDensityIsOpaqueButDarkInInverseMode :
  threadOpacity 8 ≡ 8
  ×
  inverseVoidLuminance 8 ≡ 2
highDensityIsOpaqueButDarkInInverseMode = refl , refl

data DisplayPolarity : Set where
  threadEmissionMode : DisplayPolarity
  inverseVoidMode : DisplayPolarity
  dualChannelMode : DisplayPolarity

------------------------------------------------------------------------
-- Mass-preserving sharpening and hierarchical gating.  Equal total mass with
-- changed spatial allocation represents sharpening as redistribution.  A
-- p-adic gate can lower visible mass unless the gated product is renormalised.

record TwoCellKernel : Set where
  constructor twoCellKernel
  field
    kernelLeft : Nat
    kernelRight : Nat

open TwoCellKernel public

kernelMass : TwoCellKernel → Nat
kernelMass kernel = kernelLeft kernel + kernelRight kernel

broadKernel : TwoCellKernel
broadKernel = twoCellKernel 3 3

sharpKernel : TwoCellKernel
sharpKernel = twoCellKernel 5 1

sharpeningRedistributesWithoutCreatingMass :
  kernelMass broadKernel ≡ kernelMass sharpKernel
sharpeningRedistributesWithoutCreatingMass = refl

gatedSharpKernel : TwoCellKernel
gatedSharpKernel = twoCellKernel 4 0

gatingCanReduceVisibleMass :
  kernelMass gatedSharpKernel ≡ kernelMass sharpKernel → ⊥
gatingCanReduceVisibleMass ()

renormalisedGatedKernel : TwoCellKernel
renormalisedGatedKernel = twoCellKernel 6 0

renormalisedGateRestoresEventMass :
  kernelMass renormalisedGatedKernel ≡ kernelMass sharpKernel
renormalisedGateRestoresEventMass = refl

------------------------------------------------------------------------
-- Entropy-style ambiguity and top-two ambiguity are separate symmetric score
-- families.  The finite table records their intended role without claiming a
-- real logarithm implementation.

data AmbiguityMeasure : Set where
  topTwoGapAmbiguity : AmbiguityMeasure
  allClassEntropyAmbiguity : AmbiguityMeasure

ambiguityAttenuation : AmbiguityMeasure → Nat
ambiguityAttenuation topTwoGapAmbiguity = 2
ambiguityAttenuation allClassEntropyAmbiguity = 1

entropyCanSuppressBroadMixtureMoreStrongly :
  ambiguityAttenuation allClassEntropyAmbiguity ≡ 1
entropyCanSuppressBroadMixtureMoreStrongly = refl

------------------------------------------------------------------------
-- CMYK is nonlinear.  Combining cyan and black before conversion is not the
-- same as bitwise-additive RGB combination after separate conversion.

orChannel : CMYK.BitChannel → CMYK.BitChannel → CMYK.BitChannel
orChannel CMYK.channelZero x = x
orChannel CMYK.channelOne _ = CMYK.channelOne

orRGB : CMYK.RGB → CMYK.RGB → CMYK.RGB
orRGB left right =
  CMYK.rgb
    (orChannel (CMYK.red left) (CMYK.red right))
    (orChannel (CMYK.green left) (CMYK.green right))
    (orChannel (CMYK.blue left) (CMYK.blue right))

cyanAndBlackInk : CMYK.CMYK
cyanAndBlackInk =
  CMYK.cmyk
    CMYK.channelOne
    CMYK.channelZero
    CMYK.channelZero
    CMYK.channelOne

convertedTogether : CMYK.RGB
convertedTogether = CMYK.cmykToRGB cyanAndBlackInk

convertedSeparatelyThenAdded : CMYK.RGB
convertedSeparatelyThenAdded =
  orRGB
    (CMYK.cmykToRGB CMYK.cyanInk)
    (CMYK.cmykToRGB CMYK.blackInk)

cmykConversionIsNotAdditive :
  convertedTogether ≡ convertedSeparatelyThenAdded → ⊥
cmykConversionIsNotAdditive ()

data ColourFunction : Set where
  linearAdditivePalette : ColourFunction
  nonlinearCMYKFunction : ColourFunction
  affinePCAFunction : ColourFunction
  nonlinearUMAPFunction : ColourFunction

------------------------------------------------------------------------
-- Invariance conditions are typed rather than assumed.

data TransformationLaw : Set where
  rigidFrameEquivariance : TransformationLaw
  classScaleInvariance : TransformationLaw
  padicIsometryEquivariance : TransformationLaw
  seamContinuityObligation : TransformationLaw

record RendererOutput : Set where
  constructor rendererOutput
  field
    outputColourCode : Nat
    outputLuminance : Nat
    outputOpacity : Nat

open RendererOutput public

masterRenderer : DensityBand → TopTwoGap → RendererOutput
masterRenderer band gap =
  rendererOutput
    (correctedTieFactor gap)
    (secondPassField band)
    (threadOpacity (baseField band))

canonicalMasterOutput :
  masterRenderer denseBand tiedTopTwo
  ≡
  rendererOutput 1 24 8
canonicalMasterOutput = refl

record SelfConsistentRendererBoundary : Set where
  constructor selfConsistentRendererBoundary
  field
    feedbackRendererIsOnePassClosedForm : Bool
    feedbackRendererIsOnePassClosedFormIsFalse :
      feedbackRendererIsOnePassClosedForm ≡ false

    rawGELUIsNonnegativeClassMass : Bool
    rawGELUIsNonnegativeClassMassIsFalse :
      rawGELUIsNonnegativeClassMass ≡ false

    commonTieAttenuationChangesNormalisedClassMeaning : Bool
    commonTieAttenuationChangesNormalisedClassMeaningIsFalse :
      commonTieAttenuationChangesNormalisedClassMeaning ≡ false

    decreasingSharedDepthWeightRewardsCloserBranches : Bool
    decreasingSharedDepthWeightRewardsCloserBranchesIsFalse :
      decreasingSharedDepthWeightRewardsCloserBranches ≡ false

    fixedLinearMatrixRepresentsExactCMYK : Bool
    fixedLinearMatrixRepresentsExactCMYKIsFalse :
      fixedLinearMatrixRepresentsExactCMYK ≡ false

    globalFrameMaximumPreservesCrossFrameCalibration : Bool
    globalFrameMaximumPreservesCrossFrameCalibrationIsFalse :
      globalFrameMaximumPreservesCrossFrameCalibration ≡ false

    finiteFixedPointProvesContinuumContraction : Bool
    finiteFixedPointProvesContinuumContractionIsFalse :
      finiteFixedPointProvesContinuumContraction ≡ false

open SelfConsistentRendererBoundary public

canonicalSelfConsistentRendererBoundary :
  SelfConsistentRendererBoundary
canonicalSelfConsistentRendererBoundary =
  selfConsistentRendererBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
