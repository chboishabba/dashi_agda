module DASHI.Visualisation.ColourProjectionDiagnosticsExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite diagnostics for projecting a four-dimensional simplex into three
-- display channels.

rawClassCoordinates : Nat
rawClassCoordinates = 5

simplexAffineDimension : Nat
simplexAffineDimension = 4

displayDimensions : Nat
displayDimensions = 3

unrepresentedSimplexDirections : Nat
unrepresentedSimplexDirections =
  simplexAffineDimension ∸ displayDimensions

oneSimplexDirectionIsDropped :
  unrepresentedSimplexDirections ≡ 1
oneSimplexDirectionIsDropped = refl

data ProjectionBasis : Set where
  localSlicePCA : ProjectionBasis
  globalAtlasPCA : ProjectionBasis
  fixedSemanticPalette : ProjectionBasis
  nonlinearUMAPProjection : ProjectionBasis

varianceRetained : ProjectionBasis → Nat
varianceRetained localSlicePCA = 9
varianceRetained globalAtlasPCA = 8
varianceRetained fixedSemanticPalette = 6
varianceRetained nonlinearUMAPProjection = 8

semanticStability : ProjectionBasis → Nat
semanticStability localSlicePCA = 2
semanticStability globalAtlasPCA = 8
semanticStability fixedSemanticPalette = 10
semanticStability nonlinearUMAPProjection = 3

localPCAMaximisesDeclaredVariance :
  varianceRetained localSlicePCA ≡ 9
localPCAMaximisesDeclaredVariance = refl

localPCADoesNotMaximiseSemanticStability :
  semanticStability localSlicePCA
  ≡
  semanticStability fixedSemanticPalette
  →
  ⊥
localPCADoesNotMaximiseSemanticStability ()

------------------------------------------------------------------------
-- PCA sign choices preserve represented subspaces but may reverse display
-- channels.

data PCASignChoice : Set where
  positiveSignChoice : PCASignChoice
  negativeSignChoice : PCASignChoice

record RGB3 : Set where
  constructor rgb3
  field
    redCoordinate : Nat
    greenCoordinate : Nat
    blueCoordinate : Nat

open RGB3 public

signDependentColour : PCASignChoice → RGB3
signDependentColour positiveSignChoice = rgb3 3 1 0
signDependentColour negativeSignChoice = rgb3 0 1 3

signChoiceChangesDisplayedColour :
  signDependentColour positiveSignChoice
  ≡
  signDependentColour negativeSignChoice
  →
  ⊥
signChoiceChangesDisplayedColour ()

data SliceIdentity : Set where
  sliceAlpha : SliceIdentity
  sliceBeta : SliceIdentity

localBasisSignature : SliceIdentity → Nat × Nat × Nat
localBasisSignature sliceAlpha = 1 , (2 , 3)
localBasisSignature sliceBeta = 3 , (2 , 1)

localBasesCanDiffer :
  localBasisSignature sliceAlpha
  ≡
  localBasisSignature sliceBeta
  →
  ⊥
localBasesCanDiffer ()

globalBasisSignature : SliceIdentity → Nat × Nat × Nat
globalBasisSignature sliceAlpha = 1 , (2 , 3)
globalBasisSignature sliceBeta = 1 , (2 , 3)

globalBasisIsCrossSliceStable :
  globalBasisSignature sliceAlpha
  ≡
  globalBasisSignature sliceBeta
globalBasisIsCrossSliceStable = refl

------------------------------------------------------------------------
-- Explicit mixture collision after a three-channel projection.

data FiveMixture : Set where
  mixtureA : FiveMixture
  mixtureB : FiveMixture
  mixtureC : FiveMixture

projectMixture : FiveMixture → RGB3
projectMixture mixtureA = rgb3 2 1 1
projectMixture mixtureB = rgb3 2 1 1
projectMixture mixtureC = rgb3 0 3 1

mixturesAAndBRemainDistinct : mixtureA ≡ mixtureB → ⊥
mixturesAAndBRemainDistinct ()

projectionCollision :
  projectMixture mixtureA ≡ projectMixture mixtureB
projectionCollision = refl

reconstructionResidual : FiveMixture → Nat
reconstructionResidual mixtureA = 1
reconstructionResidual mixtureB = 2
reconstructionResidual mixtureC = 0

collisionCanHideDifferentResiduals :
  reconstructionResidual mixtureA
  ≡
  reconstructionResidual mixtureB
  →
  ⊥
collisionCanHideDifferentResiduals ()

record ColourProjectionDiagnosticsBoundary : Set where
  constructor colourProjectionDiagnosticsBoundary
  field
    threeDisplayChannelsInjectivelyEncodeFourSimplexDimensions : Bool
    threeDisplayChannelsInjectivelyEncodeFourSimplexDimensionsIsFalse :
      threeDisplayChannelsInjectivelyEncodeFourSimplexDimensions ≡ false

    pcaSignIsSemanticallyCanonical : Bool
    pcaSignIsSemanticallyCanonicalIsFalse :
      pcaSignIsSemanticallyCanonical ≡ false

    localPCAProvidesCrossSliceColourIdentity : Bool
    localPCAProvidesCrossSliceColourIdentityIsFalse :
      localPCAProvidesCrossSliceColourIdentity ≡ false

    umapPreservesAllDistancesAndDensities : Bool
    umapPreservesAllDistancesAndDensitiesIsFalse :
      umapPreservesAllDistancesAndDensities ≡ false

open ColourProjectionDiagnosticsBoundary public

canonicalColourProjectionDiagnosticsBoundary :
  ColourProjectionDiagnosticsBoundary
canonicalColourProjectionDiagnosticsBoundary =
  colourProjectionDiagnosticsBoundary
    false refl
    false refl
    false refl
    false refl
