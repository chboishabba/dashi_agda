module DASHI.Physics.Closure.UltrametricBoundaryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager B task B2: ultrametric boundary receipt.
--
-- This receipt records the standard boundary theorem for Bruhat-Tits
-- trees.  The p-adic carrier boundaries are ultrametric; the archimedean
-- boundary P^1(R) with its round metric is not.  This is a geometry receipt
-- only and carries no Clay or Yang-Mills promotion.

data BoundaryAuthority : Set where
  Serre1980 :
    BoundaryAuthority

data BoundaryTheorem : Set where
  theorem :
    BoundaryAuthority →
    BoundaryTheorem

data CarrierBoundary : Set where
  P1Q3 :
    CarrierBoundary

  P1Q2 :
    CarrierBoundary

  P1Q7 :
    CarrierBoundary

canonicalCarrierUltrametricBoundaries :
  List CarrierBoundary
canonicalCarrierUltrametricBoundaries =
  P1Q3 ∷ P1Q2 ∷ P1Q7 ∷ []

data BoundaryMetricProperty : Set where
  pAdicMetric :
    BoundaryMetricProperty

  strongTriangleInequality :
    BoundaryMetricProperty

  ultrametric :
    BoundaryMetricProperty

  roundMetricNotUltrametric :
    BoundaryMetricProperty

canonicalPAdicBoundaryProperties :
  List BoundaryMetricProperty
canonicalPAdicBoundaryProperties =
  pAdicMetric
  ∷ strongTriangleInequality
  ∷ ultrametric
  ∷ []

data UltrametricBoundaryPromotion : Set where

ultrametricBoundaryPromotionImpossibleHere :
  UltrametricBoundaryPromotion →
  ⊥
ultrametricBoundaryPromotionImpossibleHere ()

gromovBoundaryStatement : String
gromovBoundaryStatement =
  "For the Bruhat-Tits tree T_p, the Gromov boundary partial_infinity T_p is P^1(Q_p)."

pAdicMetricStatement : String
pAdicMetricStatement =
  "The boundary P^1(Q_p) carries the p-adic metric d(x,y)=|x-y|_p."

strongTriangleStatement : String
strongTriangleStatement =
  "The p-adic metric satisfies the strong triangle inequality d(x,z) <= max(d(x,y), d(y,z))."

archimedeanBoundaryStatement : String
archimedeanBoundaryStatement =
  "The archimedean boundary P^1(R), with the round metric, is not ultrametric."

record UltrametricBoundaryReceipt : Setω where
  field
    boundaryTheorem :
      BoundaryTheorem

    boundaryTheoremIsSerre1980 :
      boundaryTheorem ≡ theorem Serre1980

    gromovBoundary :
      String

    gromovBoundaryIsP1Qp :
      gromovBoundary ≡ "partial_infinity T_p = P^1(Q_p)"

    pAdicBoundaryMetric :
      String

    pAdicBoundaryMetricIsCanonical :
      pAdicBoundaryMetric ≡ "d(x,y)=|x-y|_p"

    strongTriangleInequalityHolds :
      Bool

    strongTriangleInequalityHoldsIsTrue :
      strongTriangleInequalityHolds ≡ true

    pAdicBoundaryUltrametric :
      BoundaryTheorem

    pAdicBoundaryUltrametricIsTheoremSerre1980 :
      pAdicBoundaryUltrametric ≡ theorem Serre1980

    carrierUltrametricBoundaries :
      List CarrierBoundary

    carrierUltrametricBoundariesAreCanonical :
      carrierUltrametricBoundaries ≡ canonicalCarrierUltrametricBoundaries

    carrierBoundaryProperties :
      List BoundaryMetricProperty

    carrierBoundaryPropertiesAreCanonical :
      carrierBoundaryProperties ≡ canonicalPAdicBoundaryProperties

    archimedeanBoundary :
      String

    archimedeanBoundaryIsP1R :
      archimedeanBoundary ≡ "P^1(R)"

    archimedeanBoundaryMetric :
      String

    archimedeanBoundaryMetricIsRound :
      archimedeanBoundaryMetric ≡ "round metric"

    archimedeanBoundaryP1RNotUltrametric :
      Bool

    archimedeanBoundaryP1RNotUltrametricIsTrue :
      archimedeanBoundaryP1RNotUltrametric ≡ true

    archimedeanBoundaryNotUltrametricProperty :
      BoundaryMetricProperty

    archimedeanBoundaryNotUltrametricPropertyIsRoundMetricNotUltrametric :
      archimedeanBoundaryNotUltrametricProperty ≡ roundMetricNotUltrametric

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List UltrametricBoundaryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ gromovBoundaryStatement

    metricStatement :
      String

    metricStatementIsCanonical :
      metricStatement ≡ pAdicMetricStatement

    triangleStatement :
      String

    triangleStatementIsCanonical :
      triangleStatement ≡ strongTriangleStatement

    archimedeanStatement :
      String

    archimedeanStatementIsCanonical :
      archimedeanStatement ≡ archimedeanBoundaryStatement

open UltrametricBoundaryReceipt public

canonicalUltrametricBoundaryReceipt :
  UltrametricBoundaryReceipt
canonicalUltrametricBoundaryReceipt =
  record
    { boundaryTheorem =
        theorem Serre1980
    ; boundaryTheoremIsSerre1980 =
        refl
    ; gromovBoundary =
        "partial_infinity T_p = P^1(Q_p)"
    ; gromovBoundaryIsP1Qp =
        refl
    ; pAdicBoundaryMetric =
        "d(x,y)=|x-y|_p"
    ; pAdicBoundaryMetricIsCanonical =
        refl
    ; strongTriangleInequalityHolds =
        true
    ; strongTriangleInequalityHoldsIsTrue =
        refl
    ; pAdicBoundaryUltrametric =
        theorem Serre1980
    ; pAdicBoundaryUltrametricIsTheoremSerre1980 =
        refl
    ; carrierUltrametricBoundaries =
        canonicalCarrierUltrametricBoundaries
    ; carrierUltrametricBoundariesAreCanonical =
        refl
    ; carrierBoundaryProperties =
        canonicalPAdicBoundaryProperties
    ; carrierBoundaryPropertiesAreCanonical =
        refl
    ; archimedeanBoundary =
        "P^1(R)"
    ; archimedeanBoundaryIsP1R =
        refl
    ; archimedeanBoundaryMetric =
        "round metric"
    ; archimedeanBoundaryMetricIsRound =
        refl
    ; archimedeanBoundaryP1RNotUltrametric =
        true
    ; archimedeanBoundaryP1RNotUltrametricIsTrue =
        refl
    ; archimedeanBoundaryNotUltrametricProperty =
        roundMetricNotUltrametric
    ; archimedeanBoundaryNotUltrametricPropertyIsRoundMetricNotUltrametric =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; boundaryStatement =
        gromovBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; metricStatement =
        pAdicMetricStatement
    ; metricStatementIsCanonical =
        refl
    ; triangleStatement =
        strongTriangleStatement
    ; triangleStatementIsCanonical =
        refl
    ; archimedeanStatement =
        archimedeanBoundaryStatement
    ; archimedeanStatementIsCanonical =
        refl
    }

ultrametricBoundaryReceiptNoClayPromotion :
  clayYangMillsPromoted canonicalUltrametricBoundaryReceipt ≡ false
ultrametricBoundaryReceiptNoClayPromotion =
  refl

ultrametricBoundaryReceiptNoContinuumYMPromotion :
  continuumYangMillsPromoted canonicalUltrametricBoundaryReceipt ≡ false
ultrametricBoundaryReceiptNoContinuumYMPromotion =
  refl

ultrametricBoundaryReceiptNoTerminalPromotion :
  terminalClayClaimPromoted canonicalUltrametricBoundaryReceipt ≡ false
ultrametricBoundaryReceiptNoTerminalPromotion =
  refl
