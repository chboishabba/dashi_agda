module DASHI.Physics.Closure.CuspDegenerationFlatLimitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Cusp degeneration flat-limit receipt.
--
-- This receipt records the cusp-degeneration mechanism as candidate
-- geometry only.  Near a cusp of X_0(N), tau tends to i infinity and the
-- local parameter q = exp(2 pi i tau / N) tends to 0.  The Poincare metric
-- is recorded in q-coordinates, and the cusp depth supplies a candidate
-- third spatial direction, giving a local R2 x R+ flat half-space.  A full
-- R3 flat limit still needs compatibility across all cusps and is therefore
-- recorded only as a candidate, with Clay/YM promotion kept false.

data CuspDegenerationFlatLimitStatus : Set where
  cuspDegenerationLocalFlatCandidateRecordedNoClay :
    CuspDegenerationFlatLimitStatus

data CuspDegenerationFlatLimitFact : Set where
  cuspOfX0N :
    CuspDegenerationFlatLimitFact

  tauTendsToIInfinity :
    CuspDegenerationFlatLimitFact

  qEqualsExpTwoPiITauOverN :
    CuspDegenerationFlatLimitFact

  qNormTendsToZero :
    CuspDegenerationFlatLimitFact

  poincareMetricInQCoordinate :
    CuspDegenerationFlatLimitFact

  localFlatQCoordinateCandidate :
    CuspDegenerationFlatLimitFact

  cmPointsFillCuspRegionAsNTendsToInfinity :
    CuspDegenerationFlatLimitFact

  depthSuppliesThirdSpatialDirection :
    CuspDegenerationFlatLimitFact

  localHalfSpaceGeometry :
    CuspDegenerationFlatLimitFact

  fullR3NeedsAllCusps :
    CuspDegenerationFlatLimitFact

canonicalCuspDegenerationFlatLimitFacts :
  List CuspDegenerationFlatLimitFact
canonicalCuspDegenerationFlatLimitFacts =
  cuspOfX0N
  ∷ tauTendsToIInfinity
  ∷ qEqualsExpTwoPiITauOverN
  ∷ qNormTendsToZero
  ∷ poincareMetricInQCoordinate
  ∷ localFlatQCoordinateCandidate
  ∷ cmPointsFillCuspRegionAsNTendsToInfinity
  ∷ depthSuppliesThirdSpatialDirection
  ∷ localHalfSpaceGeometry
  ∷ fullR3NeedsAllCusps
  ∷ []

data FullFlatLimitStatus : Set where
  candidate :
    FullFlatLimitStatus

data CuspDegenerationFlatLimitPromotion : Set where

cuspDegenerationFlatLimitPromotionImpossibleHere :
  CuspDegenerationFlatLimitPromotion →
  ⊥
cuspDegenerationFlatLimitPromotionImpossibleHere ()

cuspCoordinateStatement :
  String
cuspCoordinateStatement =
  "Near a cusp of X_0(N), tau -> i infinity and q = exp(2 pi i tau / N), so |q| -> 0."

cuspPoincareMetricStatement :
  String
cuspPoincareMetricStatement =
  "Poincare metric: ds^2 = |d tau|^2/(Im tau)^2 = |dq|^2/(N^2 |q|^2 |log |q||^2)."

cuspLocalFlatStatement :
  String
cuspLocalFlatStatement =
  "As |q| -> 0, the q-coordinate cusp degeneration is recorded as asymptotically/local flat geometry, candidate only."

cuspCMFillingStatement :
  String
cuspCMFillingStatement =
  "CM points at level N near the cusp fill the cusp region as N -> infinity."

cuspDepthStatement :
  String
cuspDepthStatement =
  "The third spatial direction is supplied by cusp depth; local geometry is R2 x R+ flat half-space."

cuspFullFlatLimitStatement :
  String
cuspFullFlatLimitStatement =
  "A full R3 flat limit needs compatibility across all cusps, so it remains candidate-only."

record CuspDegenerationFlatLimitReceipt : Setω where
  field
    status :
      CuspDegenerationFlatLimitStatus

    facts :
      List CuspDegenerationFlatLimitFact

    factsAreCanonical :
      facts ≡ canonicalCuspDegenerationFlatLimitFacts

    modularCurve :
      String

    modularCurveIsX0N :
      modularCurve ≡ "X_0(N)"

    cuspLimit :
      String

    cuspLimitIsTauToIInfinity :
      cuspLimit ≡ "tau -> i infinity"

    qCoordinate :
      String

    qCoordinateIsCanonical :
      qCoordinate ≡ "q = exp(2 pi i tau / N)"

    qNormLimit :
      String

    qNormLimitIsZero :
      qNormLimit ≡ "|q| -> 0"

    poincareMetricExpression :
      String

    poincareMetricExpressionIsCanonical :
      poincareMetricExpression ≡ cuspPoincareMetricStatement

    asymptoticallyLocalFlatInQCoordinate :
      Bool

    asymptoticallyLocalFlatInQCoordinateIsTrue :
      asymptoticallyLocalFlatInQCoordinate ≡ true

    cuspDegenerationGivesLocalFlatGeometry :
      Bool

    cuspDegenerationGivesLocalFlatGeometryIsTrue :
      cuspDegenerationGivesLocalFlatGeometry ≡ true

    cmPointsNearCuspFillCuspRegionAsNTendsToInfinity :
      Bool

    cmPointsNearCuspFillCuspRegionAsNTendsToInfinityIsTrue :
      cmPointsNearCuspFillCuspRegionAsNTendsToInfinity ≡ true

    thirdSpatialDirectionFromDepth :
      Bool

    thirdSpatialDirectionFromDepthIsTrue :
      thirdSpatialDirectionFromDepth ≡ true

    localGeometryNearCusp :
      String

    localGeometryNearCuspIsR2xRPlus :
      localGeometryNearCusp ≡ "R2 x R+"

    localGeometryNearCuspIsFlatHalfSpace :
      Bool

    localGeometryNearCuspIsFlatHalfSpaceIsTrue :
      localGeometryNearCuspIsFlatHalfSpace ≡ true

    fullFlatLimit :
      FullFlatLimitStatus

    fullFlatLimitIsCandidate :
      fullFlatLimit ≡ candidate

    fullR3FlatLimitNeedsAllCusps :
      Bool

    fullR3FlatLimitNeedsAllCuspsIsTrue :
      fullR3FlatLimitNeedsAllCusps ≡ true

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    ymClayPromotion :
      Bool

    ymClayPromotionIsFalse :
      ymClayPromotion ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List CuspDegenerationFlatLimitPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    cuspCoordinateStatementField :
      String

    cuspCoordinateStatementFieldIsCanonical :
      cuspCoordinateStatementField ≡ cuspCoordinateStatement

    cuspLocalFlatStatementField :
      String

    cuspLocalFlatStatementFieldIsCanonical :
      cuspLocalFlatStatementField ≡ cuspLocalFlatStatement

    cuspCMFillingStatementField :
      String

    cuspCMFillingStatementFieldIsCanonical :
      cuspCMFillingStatementField ≡ cuspCMFillingStatement

    cuspDepthStatementField :
      String

    cuspDepthStatementFieldIsCanonical :
      cuspDepthStatementField ≡ cuspDepthStatement

    cuspFullFlatLimitStatementField :
      String

    cuspFullFlatLimitStatementFieldIsCanonical :
      cuspFullFlatLimitStatementField ≡ cuspFullFlatLimitStatement

    receiptBoundary :
      List String

open CuspDegenerationFlatLimitReceipt public

canonicalCuspDegenerationFlatLimitReceipt :
  CuspDegenerationFlatLimitReceipt
canonicalCuspDegenerationFlatLimitReceipt =
  record
    { status =
        cuspDegenerationLocalFlatCandidateRecordedNoClay
    ; facts =
        canonicalCuspDegenerationFlatLimitFacts
    ; factsAreCanonical =
        refl
    ; modularCurve =
        "X_0(N)"
    ; modularCurveIsX0N =
        refl
    ; cuspLimit =
        "tau -> i infinity"
    ; cuspLimitIsTauToIInfinity =
        refl
    ; qCoordinate =
        "q = exp(2 pi i tau / N)"
    ; qCoordinateIsCanonical =
        refl
    ; qNormLimit =
        "|q| -> 0"
    ; qNormLimitIsZero =
        refl
    ; poincareMetricExpression =
        cuspPoincareMetricStatement
    ; poincareMetricExpressionIsCanonical =
        refl
    ; asymptoticallyLocalFlatInQCoordinate =
        true
    ; asymptoticallyLocalFlatInQCoordinateIsTrue =
        refl
    ; cuspDegenerationGivesLocalFlatGeometry =
        true
    ; cuspDegenerationGivesLocalFlatGeometryIsTrue =
        refl
    ; cmPointsNearCuspFillCuspRegionAsNTendsToInfinity =
        true
    ; cmPointsNearCuspFillCuspRegionAsNTendsToInfinityIsTrue =
        refl
    ; thirdSpatialDirectionFromDepth =
        true
    ; thirdSpatialDirectionFromDepthIsTrue =
        refl
    ; localGeometryNearCusp =
        "R2 x R+"
    ; localGeometryNearCuspIsR2xRPlus =
        refl
    ; localGeometryNearCuspIsFlatHalfSpace =
        true
    ; localGeometryNearCuspIsFlatHalfSpaceIsTrue =
        refl
    ; fullFlatLimit =
        candidate
    ; fullFlatLimitIsCandidate =
        refl
    ; fullR3FlatLimitNeedsAllCusps =
        true
    ; fullR3FlatLimitNeedsAllCuspsIsTrue =
        refl
    ; continuumYangMillsConstructed =
        false
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; ymClayPromotion =
        false
    ; ymClayPromotionIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; cuspCoordinateStatementField =
        cuspCoordinateStatement
    ; cuspCoordinateStatementFieldIsCanonical =
        refl
    ; cuspLocalFlatStatementField =
        cuspLocalFlatStatement
    ; cuspLocalFlatStatementFieldIsCanonical =
        refl
    ; cuspCMFillingStatementField =
        cuspCMFillingStatement
    ; cuspCMFillingStatementFieldIsCanonical =
        refl
    ; cuspDepthStatementField =
        cuspDepthStatement
    ; cuspDepthStatementFieldIsCanonical =
        refl
    ; cuspFullFlatLimitStatementField =
        cuspFullFlatLimitStatement
    ; cuspFullFlatLimitStatementFieldIsCanonical =
        refl
    ; receiptBoundary =
        "Cusp degeneration gives a local flat geometry candidate near q = 0"
        ∷ "Near a cusp of X_0(N), tau -> i infinity, q = exp(2 pi i tau / N), and |q| -> 0"
        ∷ "Poincare metric is recorded as ds^2 = |d tau|^2/(Im tau)^2 = |dq|^2/(N^2 |q|^2 |log |q||^2)"
        ∷ "CM points near the cusp fill the cusp region as N -> infinity"
        ∷ "Depth supplies the third spatial direction, giving local geometry R2 x R+"
        ∷ "Full R3 flat limit requires all cusps and remains candidate-only"
        ∷ "Continuum YM, Clay YM, and terminal Clay promotion remain false"
        ∷ []
    }

cuspDegenerationGivesLocalFlatGeometryIsTrueForCanonical :
  cuspDegenerationGivesLocalFlatGeometry
    canonicalCuspDegenerationFlatLimitReceipt
  ≡ true
cuspDegenerationGivesLocalFlatGeometryIsTrueForCanonical =
  refl

localGeometryNearCuspIsR2xRPlusForCanonical :
  localGeometryNearCusp canonicalCuspDegenerationFlatLimitReceipt
  ≡ "R2 x R+"
localGeometryNearCuspIsR2xRPlusForCanonical =
  refl

fullFlatLimitIsCandidateForCanonical :
  fullFlatLimit canonicalCuspDegenerationFlatLimitReceipt
  ≡ candidate
fullFlatLimitIsCandidateForCanonical =
  refl

cuspDegenerationKeepsClayYangMillsFalse :
  clayYangMillsPromoted canonicalCuspDegenerationFlatLimitReceipt
  ≡ false
cuspDegenerationKeepsClayYangMillsFalse =
  refl

cuspDegenerationKeepsYMPromotionFalse :
  ymClayPromotion canonicalCuspDegenerationFlatLimitReceipt
  ≡ false
cuspDegenerationKeepsYMPromotionFalse =
  refl
