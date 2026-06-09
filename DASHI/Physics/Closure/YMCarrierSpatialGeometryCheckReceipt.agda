module DASHI.Physics.Closure.YMCarrierSpatialGeometryCheckReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yang-Mills carrier spatial geometry check receipt.
--
-- This receipt records the mismatch between the carrier geometry and the
-- standard Poincare model geometry relevant for four-dimensional Euclidean
-- Yang-Mills.  The carrier is the product geometry H3 x R+ with product
-- metric, so its spatial slices are H3 with curvature -1.  Poincare H4 is a
-- warped product R3 x_t R+ whose fixed-t slices are flat R3 with curvature 0.
--
-- Four-dimensional YM conformal invariance does not erase this mismatch by a
-- three-dimensional slice argument.  It would help only if the carrier spatial
-- geometry were flat R3, or if the carrier were globally conformally
-- equivalent in the relevant four-dimensional sense to the Poincare H4
-- geometry.  Neither condition is recorded for the present carrier, so the
-- archimedean geometry gap persists.

data YMCarrierSpatialGeometryCheckStatus : Set where
  carrierPoincareGeometryMismatchRecorded :
    YMCarrierSpatialGeometryCheckStatus

data YMCarrierGeometry : Set where
  H3xRPlusProductMetric :
    YMCarrierGeometry

data YMPoincareGeometry : Set where
  H4PoincareWarpedR3xTRPlus :
    YMPoincareGeometry

data YMSpatialSliceGeometry : Set where
  H3SpatialSlice :
    YMSpatialSliceGeometry

  R3SpatialSlice :
    YMSpatialSliceGeometry

data YMSpatialCurvature : Set where
  curvatureMinusOne :
    YMSpatialCurvature

  curvatureZero :
    YMSpatialCurvature

data YMConformalInvarianceCondition : Set where
  conditionCarrierSpatialGeometryFlatR3 :
    YMConformalInvarianceCondition

  conditionGloballyConformallyEquivalentInRelevant4DYMGeometry :
    YMConformalInvarianceCondition

canonicalYMConformalInvarianceConditions :
  List YMConformalInvarianceCondition
canonicalYMConformalInvarianceConditions =
  conditionCarrierSpatialGeometryFlatR3
  ∷ conditionGloballyConformallyEquivalentInRelevant4DYMGeometry
  ∷ []

data YMCarrierSpatialGeometryMismatchFact : Set where
  carrierIsH3xRPlusProductMetric :
    YMCarrierSpatialGeometryMismatchFact

  poincareH4IsWarpedR3xTRPlus :
    YMCarrierSpatialGeometryMismatchFact

  carrierSpatialSlicesHaveCurvatureMinusOne :
    YMCarrierSpatialGeometryMismatchFact

  poincareSpatialSlicesHaveCurvatureZero :
    YMCarrierSpatialGeometryMismatchFact

  threeDimensionalSliceConformalArgumentDoesNotApplyToFourDimensionalYM :
    YMCarrierSpatialGeometryMismatchFact

  requiredFlatOrGlobalFourDimensionalConformalEquivalenceMissing :
    YMCarrierSpatialGeometryMismatchFact

canonicalYMCarrierSpatialGeometryMismatchFacts :
  List YMCarrierSpatialGeometryMismatchFact
canonicalYMCarrierSpatialGeometryMismatchFacts =
  carrierIsH3xRPlusProductMetric
  ∷ poincareH4IsWarpedR3xTRPlus
  ∷ carrierSpatialSlicesHaveCurvatureMinusOne
  ∷ poincareSpatialSlicesHaveCurvatureZero
  ∷ threeDimensionalSliceConformalArgumentDoesNotApplyToFourDimensionalYM
  ∷ requiredFlatOrGlobalFourDimensionalConformalEquivalenceMissing
  ∷ []

data YMCarrierSpatialGeometryPromotion : Set where

ymCarrierSpatialGeometryPromotionImpossibleHere :
  YMCarrierSpatialGeometryPromotion →
  ⊥
ymCarrierSpatialGeometryPromotionImpossibleHere ()

carrierGeometryMismatchStatement : String
carrierGeometryMismatchStatement =
  "Carrier geometry is H3 x R+ with product metric, while Poincare H4 is the warped product R3 x_t R+."

spatialSliceCurvatureMismatchStatement : String
spatialSliceCurvatureMismatchStatement =
  "Carrier spatial slices are H3 with curvature -1; Poincare H4 fixed-t slices are R3 with curvature 0."

ymConformalInvarianceBoundaryStatement : String
ymConformalInvarianceBoundaryStatement =
  "Four-dimensional YM conformal invariance helps only for flat R3 carrier spatial geometry or a relevant global four-dimensional conformal equivalence; this is not the present carrier."

record YMCarrierSpatialGeometryCheckReceipt : Setω where
  field
    status :
      YMCarrierSpatialGeometryCheckStatus

    carrierGeometry :
      YMCarrierGeometry

    carrierGeometryIsH3xRPlusProductMetric :
      carrierGeometry ≡ H3xRPlusProductMetric

    poincareGeometry :
      YMPoincareGeometry

    poincareGeometryIsH4WarpedR3xTRPlus :
      poincareGeometry ≡ H4PoincareWarpedR3xTRPlus

    carrierSpatialSlice :
      YMSpatialSliceGeometry

    carrierSpatialSliceIsH3 :
      carrierSpatialSlice ≡ H3SpatialSlice

    poincareSpatialSlice :
      YMSpatialSliceGeometry

    poincareSpatialSliceIsR3 :
      poincareSpatialSlice ≡ R3SpatialSlice

    carrierSpatialCurvature :
      YMSpatialCurvature

    carrierSpatialCurvatureIsMinusOne :
      carrierSpatialCurvature ≡ curvatureMinusOne

    poincareSpatialCurvature :
      YMSpatialCurvature

    poincareSpatialCurvatureIsZero :
      poincareSpatialCurvature ≡ curvatureZero

    carrierGeometryH3xRPlusNotEqualH4Poincare :
      Bool

    carrierGeometryH3xRPlusNotEqualH4PoincareIsTrue :
      carrierGeometryH3xRPlusNotEqualH4Poincare ≡ true

    threeDConformalInvarianceDoesNotApplyToYM :
      Bool

    threeDConformalInvarianceDoesNotApplyToYMIsTrue :
      threeDConformalInvarianceDoesNotApplyToYM ≡ true

    archimedeanGapPersists :
      Bool

    archimedeanGapPersistsIsTrue :
      archimedeanGapPersists ≡ true

    carrierSpatialGeometryFlatR3 :
      Bool

    carrierSpatialGeometryFlatR3IsFalse :
      carrierSpatialGeometryFlatR3 ≡ false

    relevantGlobal4DConformalEquivalence :
      Bool

    relevantGlobal4DConformalEquivalenceIsFalse :
      relevantGlobal4DConformalEquivalence ≡ false

    conformalInvarianceHelpfulConditions :
      List YMConformalInvarianceCondition

    conformalInvarianceHelpfulConditionsAreCanonical :
      conformalInvarianceHelpfulConditions
      ≡
      canonicalYMConformalInvarianceConditions

    mismatchFacts :
      List YMCarrierSpatialGeometryMismatchFact

    mismatchFactsAreCanonical :
      mismatchFacts
      ≡
      canonicalYMCarrierSpatialGeometryMismatchFacts

    carrierGeometryMismatchStatementField :
      String

    carrierGeometryMismatchStatementIsCanonical :
      carrierGeometryMismatchStatementField
      ≡
      carrierGeometryMismatchStatement

    spatialSliceCurvatureMismatchStatementField :
      String

    spatialSliceCurvatureMismatchStatementIsCanonical :
      spatialSliceCurvatureMismatchStatementField
      ≡
      spatialSliceCurvatureMismatchStatement

    ymConformalInvarianceBoundaryStatementField :
      String

    ymConformalInvarianceBoundaryStatementIsCanonical :
      ymConformalInvarianceBoundaryStatementField
      ≡
      ymConformalInvarianceBoundaryStatement

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalYMPromoted :
      Bool

    terminalYMPromotedIsFalse :
      terminalYMPromoted ≡ false

    promotionFlags :
      List YMCarrierSpatialGeometryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMCarrierSpatialGeometryCheckReceipt public

canonicalYMCarrierSpatialGeometryCheckReceipt :
  YMCarrierSpatialGeometryCheckReceipt
canonicalYMCarrierSpatialGeometryCheckReceipt =
  record
    { status =
        carrierPoincareGeometryMismatchRecorded
    ; carrierGeometry =
        H3xRPlusProductMetric
    ; carrierGeometryIsH3xRPlusProductMetric =
        refl
    ; poincareGeometry =
        H4PoincareWarpedR3xTRPlus
    ; poincareGeometryIsH4WarpedR3xTRPlus =
        refl
    ; carrierSpatialSlice =
        H3SpatialSlice
    ; carrierSpatialSliceIsH3 =
        refl
    ; poincareSpatialSlice =
        R3SpatialSlice
    ; poincareSpatialSliceIsR3 =
        refl
    ; carrierSpatialCurvature =
        curvatureMinusOne
    ; carrierSpatialCurvatureIsMinusOne =
        refl
    ; poincareSpatialCurvature =
        curvatureZero
    ; poincareSpatialCurvatureIsZero =
        refl
    ; carrierGeometryH3xRPlusNotEqualH4Poincare =
        true
    ; carrierGeometryH3xRPlusNotEqualH4PoincareIsTrue =
        refl
    ; threeDConformalInvarianceDoesNotApplyToYM =
        true
    ; threeDConformalInvarianceDoesNotApplyToYMIsTrue =
        refl
    ; archimedeanGapPersists =
        true
    ; archimedeanGapPersistsIsTrue =
        refl
    ; carrierSpatialGeometryFlatR3 =
        false
    ; carrierSpatialGeometryFlatR3IsFalse =
        refl
    ; relevantGlobal4DConformalEquivalence =
        false
    ; relevantGlobal4DConformalEquivalenceIsFalse =
        refl
    ; conformalInvarianceHelpfulConditions =
        canonicalYMConformalInvarianceConditions
    ; conformalInvarianceHelpfulConditionsAreCanonical =
        refl
    ; mismatchFacts =
        canonicalYMCarrierSpatialGeometryMismatchFacts
    ; mismatchFactsAreCanonical =
        refl
    ; carrierGeometryMismatchStatementField =
        carrierGeometryMismatchStatement
    ; carrierGeometryMismatchStatementIsCanonical =
        refl
    ; spatialSliceCurvatureMismatchStatementField =
        spatialSliceCurvatureMismatchStatement
    ; spatialSliceCurvatureMismatchStatementIsCanonical =
        refl
    ; ymConformalInvarianceBoundaryStatementField =
        ymConformalInvarianceBoundaryStatement
    ; ymConformalInvarianceBoundaryStatementIsCanonical =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalYMPromoted =
        false
    ; terminalYMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records carrier geometry H3 x R+ product metric versus Poincare H4 warped product R3 x_t R+"
        ∷ "Records curvature mismatch: H3 spatial slices have curvature -1, while Poincare fixed-t R3 slices have curvature 0"
        ∷ "Records that a three-dimensional conformal-slice argument does not supply four-dimensional YM conformal equivalence"
        ∷ "Records no Clay YM or terminal promotion; the archimedean geometry gap persists"
        ∷ []
    }

carrierGeometryH3xRPlusNotEqualH4PoincareTrue :
  carrierGeometryH3xRPlusNotEqualH4Poincare
    canonicalYMCarrierSpatialGeometryCheckReceipt
  ≡
  true
carrierGeometryH3xRPlusNotEqualH4PoincareTrue =
  refl

threeDConformalInvarianceDoesNotApplyToYMTrue :
  threeDConformalInvarianceDoesNotApplyToYM
    canonicalYMCarrierSpatialGeometryCheckReceipt
  ≡
  true
threeDConformalInvarianceDoesNotApplyToYMTrue =
  refl

archimedeanGapPersistsTrue :
  archimedeanGapPersists canonicalYMCarrierSpatialGeometryCheckReceipt
  ≡
  true
archimedeanGapPersistsTrue =
  refl

carrierSpatialCurvatureMinusOneRecorded :
  carrierSpatialCurvature canonicalYMCarrierSpatialGeometryCheckReceipt
  ≡
  curvatureMinusOne
carrierSpatialCurvatureMinusOneRecorded =
  refl

poincareSpatialCurvatureZeroRecorded :
  poincareSpatialCurvature canonicalYMCarrierSpatialGeometryCheckReceipt
  ≡
  curvatureZero
poincareSpatialCurvatureZeroRecorded =
  refl
