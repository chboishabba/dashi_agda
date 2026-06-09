module DASHI.Physics.Closure.ShimuraTowerUniversalityClassReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ShimuraTowerContinuumLimitReceipt as Continuum
import DASHI.Physics.Closure.ShimuraTowerSpatialLatticeReceipt as Spatial

------------------------------------------------------------------------
-- Shimura-tower universality-class obstruction receipt.
--
-- B1 records a carrier-native Shimura-tower spatial refinement.  B2 records
-- the inverse/infinite-level tower as locally Euclidean below its curvature
-- radius.  This receipt records the physical-scale conclusion: for the
-- carrier length scale Lambda_c^-1 about 0.12 fm and QCD scale about 1 fm,
-- the QCD scale is larger than the curvature radius, so curvature remains
-- relevant at QCD scales.  Therefore Shimura-tower Yang-Mills is not
-- identified with Euclidean Yang-Mills at physical QCD scales.

data ShimuraTowerUniversalityClassStatus : Set where
  shimuraTowerDifferentFromEuclideanAtQCDScalesNoPromotion :
    ShimuraTowerUniversalityClassStatus

data PhysicalScaleTruth : Set where
  trueAtPhysicalScales :
    PhysicalScaleTruth

data ShimuraTowerUniversalityClassObstructionStatus : Set where
  confirmed :
    ShimuraTowerUniversalityClassObstructionStatus

data ShimuraTowerUniversalityClassInput : Set where
  b1ShimuraTowerSpatialRefinement :
    ShimuraTowerUniversalityClassInput

  b2ShimuraTowerLocallyEuclideanBelowCurvatureRadius :
    ShimuraTowerUniversalityClassInput

  carrierLengthScaleLambdaCInverseAbout012Fm :
    ShimuraTowerUniversalityClassInput

  qcdScaleAbout1Fm :
    ShimuraTowerUniversalityClassInput

canonicalShimuraTowerUniversalityClassInputs :
  List ShimuraTowerUniversalityClassInput
canonicalShimuraTowerUniversalityClassInputs =
  b1ShimuraTowerSpatialRefinement
  ∷ b2ShimuraTowerLocallyEuclideanBelowCurvatureRadius
  ∷ carrierLengthScaleLambdaCInverseAbout012Fm
  ∷ qcdScaleAbout1Fm
  ∷ []

data ShimuraTowerUniversalityClassConclusion : Set where
  towerLocallyEuclideanOnlyBelowCurvatureRadius :
    ShimuraTowerUniversalityClassConclusion

  physicalQCDScaleLargerThanCurvatureRadiusConclusion :
    ShimuraTowerUniversalityClassConclusion

  curvatureRelevantAtQCDScaleConclusion :
    ShimuraTowerUniversalityClassConclusion

  shimuraTowerYMDifferentFromEuclideanYMAtPhysicalScales :
    ShimuraTowerUniversalityClassConclusion

canonicalShimuraTowerUniversalityClassConclusions :
  List ShimuraTowerUniversalityClassConclusion
canonicalShimuraTowerUniversalityClassConclusions =
  towerLocallyEuclideanOnlyBelowCurvatureRadius
  ∷ physicalQCDScaleLargerThanCurvatureRadiusConclusion
  ∷ curvatureRelevantAtQCDScaleConclusion
  ∷ shimuraTowerYMDifferentFromEuclideanYMAtPhysicalScales
  ∷ []

data ShimuraTowerUniversalityClassPromotion : Set where

shimuraTowerUniversalityClassPromotionImpossibleHere :
  ShimuraTowerUniversalityClassPromotion →
  ⊥
shimuraTowerUniversalityClassPromotionImpossibleHere ()

carrierLengthScaleLabel : String
carrierLengthScaleLabel =
  "Lambda_c^-1 ~ 0.12 fm"

qcdScaleLabel : String
qcdScaleLabel =
  "QCD scale ~ 1 fm"

curvatureRadiusComparisonLabel : String
curvatureRadiusComparisonLabel =
  "1 fm QCD scale is larger than the Shimura-tower curvature radius associated with Lambda_c^-1 ~ 0.12 fm"

shimuraTowerUniversalityClassStatement : String
shimuraTowerUniversalityClassStatement =
  "The Shimura tower is locally Euclidean below curvature radius, but at physical QCD scales the QCD length scale is larger than the curvature radius; curvature is relevant, so Shimura-tower Yang-Mills is not equivalent to Euclidean Yang-Mills at physical scales."

record ShimuraTowerUniversalityClassReceipt : Setω where
  field
    status :
      ShimuraTowerUniversalityClassStatus

    spatialReceipt :
      Spatial.ShimuraTowerSpatialLatticeReceipt

    spatialRefinementFromB1 :
      Spatial.spatialLatticeRefinable spatialReceipt ≡ true

    continuumReceipt :
      Continuum.ShimuraTowerContinuumLimitReceipt

    continuumTowerFromB2 :
      Continuum.ymCarrierNativeContinuumLimitDefined continuumReceipt
      ≡
      Continuum.candidate

    b2TowerSpacingGoesTo0 :
      Continuum.spacingGoesTo0 continuumReceipt ≡ true

    towerLocallyEuclideanBelowCurvatureRadius :
      Bool

    towerLocallyEuclideanBelowCurvatureRadiusIsTrue :
      towerLocallyEuclideanBelowCurvatureRadius ≡ true

    carrierLengthScale :
      String

    carrierLengthScaleIsCanonical :
      carrierLengthScale ≡ carrierLengthScaleLabel

    qcdScale :
      String

    qcdScaleIsCanonical :
      qcdScale ≡ qcdScaleLabel

    physicalQCDScaleLargerThanCurvatureRadius :
      Bool

    physicalQCDScaleLargerThanCurvatureRadiusIsTrue :
      physicalQCDScaleLargerThanCurvatureRadius ≡ true

    curvatureRadiusComparison :
      String

    curvatureRadiusComparisonIsCanonical :
      curvatureRadiusComparison ≡ curvatureRadiusComparisonLabel

    curvatureRelevantAtQCDScale :
      Bool

    curvatureRelevantAtQCDScaleIsTrue :
      curvatureRelevantAtQCDScale ≡ true

    shimuraTowerUniversalityClass :
      Bool

    differentFromEuclideanAtQCDScales :
      shimuraTowerUniversalityClass ≡ true

    ymShimuraTowerNotEquivalentToEuclideanYM :
      PhysicalScaleTruth

    ymShimuraTowerNotEquivalentToEuclideanYMAtPhysicalScales :
      ymShimuraTowerNotEquivalentToEuclideanYM ≡ trueAtPhysicalScales

    ymShimuraTowerUniversalityClassObstruction :
      ShimuraTowerUniversalityClassObstructionStatus

    ymShimuraTowerUniversalityClassObstructionConfirmed :
      ymShimuraTowerUniversalityClassObstruction ≡ confirmed

    inputs :
      List ShimuraTowerUniversalityClassInput

    inputsAreCanonical :
      inputs ≡ canonicalShimuraTowerUniversalityClassInputs

    conclusions :
      List ShimuraTowerUniversalityClassConclusion

    conclusionsAreCanonical :
      conclusions ≡ canonicalShimuraTowerUniversalityClassConclusions

    universalityClassPromoted :
      Bool

    universalityClassPromotedIsFalse :
      universalityClassPromoted ≡ false

    euclideanYMEquivalencePromoted :
      Bool

    euclideanYMEquivalencePromotedIsFalse :
      euclideanYMEquivalencePromoted ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ shimuraTowerUniversalityClassStatement

    promotionFlags :
      List ShimuraTowerUniversalityClassPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ShimuraTowerUniversalityClassReceipt public

canonicalShimuraTowerUniversalityClassReceipt :
  ShimuraTowerUniversalityClassReceipt
canonicalShimuraTowerUniversalityClassReceipt =
  record
    { status =
        shimuraTowerDifferentFromEuclideanAtQCDScalesNoPromotion
    ; spatialReceipt =
        Spatial.canonicalShimuraTowerSpatialLatticeReceipt
    ; spatialRefinementFromB1 =
        refl
    ; continuumReceipt =
        Continuum.canonicalShimuraTowerContinuumLimitReceipt
    ; continuumTowerFromB2 =
        refl
    ; b2TowerSpacingGoesTo0 =
        refl
    ; towerLocallyEuclideanBelowCurvatureRadius =
        true
    ; towerLocallyEuclideanBelowCurvatureRadiusIsTrue =
        refl
    ; carrierLengthScale =
        carrierLengthScaleLabel
    ; carrierLengthScaleIsCanonical =
        refl
    ; qcdScale =
        qcdScaleLabel
    ; qcdScaleIsCanonical =
        refl
    ; physicalQCDScaleLargerThanCurvatureRadius =
        true
    ; physicalQCDScaleLargerThanCurvatureRadiusIsTrue =
        refl
    ; curvatureRadiusComparison =
        curvatureRadiusComparisonLabel
    ; curvatureRadiusComparisonIsCanonical =
        refl
    ; curvatureRelevantAtQCDScale =
        true
    ; curvatureRelevantAtQCDScaleIsTrue =
        refl
    ; shimuraTowerUniversalityClass =
        true
    ; differentFromEuclideanAtQCDScales =
        refl
    ; ymShimuraTowerNotEquivalentToEuclideanYM =
        trueAtPhysicalScales
    ; ymShimuraTowerNotEquivalentToEuclideanYMAtPhysicalScales =
        refl
    ; ymShimuraTowerUniversalityClassObstruction =
        confirmed
    ; ymShimuraTowerUniversalityClassObstructionConfirmed =
        refl
    ; inputs =
        canonicalShimuraTowerUniversalityClassInputs
    ; inputsAreCanonical =
        refl
    ; conclusions =
        canonicalShimuraTowerUniversalityClassConclusions
    ; conclusionsAreCanonical =
        refl
    ; universalityClassPromoted =
        false
    ; universalityClassPromotedIsFalse =
        refl
    ; euclideanYMEquivalencePromoted =
        false
    ; euclideanYMEquivalencePromotedIsFalse =
        refl
    ; continuumYangMillsConstructed =
        false
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        shimuraTowerUniversalityClassStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "B1 supplies the Shimura tower spatial-refinement candidate"
        ∷ "B2 supplies the inverse/infinite-level tower and local Euclidean behaviour below curvature radius"
        ∷ "The physical QCD scale is recorded as about 1 fm, larger than the Lambda_c^-1 carrier scale about 0.12 fm"
        ∷ "Curvature is relevant at QCD scales, so Shimura-tower YM is different from Euclidean YM at physical scales"
        ∷ "The obstruction is confirmed, but no universality, Euclidean-equivalence, continuum-YM, Clay, or terminal promotion follows"
        ∷ []
    }

shimuraTowerUniversalityClassDifferentFromEuclideanAtQCDScales :
  shimuraTowerUniversalityClass canonicalShimuraTowerUniversalityClassReceipt
  ≡
  true
shimuraTowerUniversalityClassDifferentFromEuclideanAtQCDScales =
  refl

shimuraTowerCurvatureRelevantAtQCDScale :
  curvatureRelevantAtQCDScale canonicalShimuraTowerUniversalityClassReceipt
  ≡
  true
shimuraTowerCurvatureRelevantAtQCDScale =
  refl

shimuraTowerYMNotEquivalentToEuclideanYMAtPhysicalScales :
  ymShimuraTowerNotEquivalentToEuclideanYM
    canonicalShimuraTowerUniversalityClassReceipt
  ≡
  trueAtPhysicalScales
shimuraTowerYMNotEquivalentToEuclideanYMAtPhysicalScales =
  refl

shimuraTowerUniversalityClassObstructionConfirmed :
  ymShimuraTowerUniversalityClassObstruction
    canonicalShimuraTowerUniversalityClassReceipt
  ≡
  confirmed
shimuraTowerUniversalityClassObstructionConfirmed =
  refl

shimuraTowerUniversalityClassKeepsPromotionsFalse :
  universalityClassPromoted canonicalShimuraTowerUniversalityClassReceipt
  ≡
  false
shimuraTowerUniversalityClassKeepsPromotionsFalse =
  refl

shimuraTowerUniversalityClassKeepsClayFalse :
  clayYangMillsPromoted canonicalShimuraTowerUniversalityClassReceipt
  ≡
  false
shimuraTowerUniversalityClassKeepsClayFalse =
  refl
