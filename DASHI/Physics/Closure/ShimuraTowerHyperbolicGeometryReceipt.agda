module DASHI.Physics.Closure.ShimuraTowerHyperbolicGeometryReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Hyperbolic geometry of the Shimura tower.
--
-- This receipt records the metric geometry carried by the 3/4/7 Shimura
-- tower.  It deliberately separates the hyperbolic carrier from Euclidean
-- Yang--Mills: the universality-class comparison is left open, and no Clay
-- Yang--Mills or terminal Clay promotion is made here.

data ShimuraTowerHyperbolicGeometryStatus : Set where
  shimuraTowerHyperbolicGeometryRecordedNoClay :
    ShimuraTowerHyperbolicGeometryStatus

data ShimuraTowerHyperbolicFactor : Set where
  X0-3^k :
    ShimuraTowerHyperbolicFactor

  X0-4^k :
    ShimuraTowerHyperbolicFactor

  X0-7^k :
    ShimuraTowerHyperbolicFactor

canonicalShimuraTowerHyperbolicFactors :
  List ShimuraTowerHyperbolicFactor
canonicalShimuraTowerHyperbolicFactors =
  X0-3^k
  ∷ X0-4^k
  ∷ X0-7^k
  ∷ []

data ShimuraTowerMetricFact : Set where
  modularCurveX0NHasPoincareMetricCurvatureMinusOne :
    ShimuraTowerMetricFact

  productX0-3^kX0-4^kX0-7^kHasProductHyperbolicMetric :
    ShimuraTowerMetricFact

  infiniteTowerDenseCMPointGeometryIsHyperbolicNotEuclidean :
    ShimuraTowerMetricFact

  hyperbolicLaplacianSpectrumStartsAtOneQuarter :
    ShimuraTowerMetricFact

  euclideanLaplacianSpectrumStartsAtZero :
    ShimuraTowerMetricFact

  hyperbolicYangMillsNotSameAsEuclideanYangMills :
    ShimuraTowerMetricFact

canonicalShimuraTowerMetricFacts :
  List ShimuraTowerMetricFact
canonicalShimuraTowerMetricFacts =
  modularCurveX0NHasPoincareMetricCurvatureMinusOne
  ∷ productX0-3^kX0-4^kX0-7^kHasProductHyperbolicMetric
  ∷ infiniteTowerDenseCMPointGeometryIsHyperbolicNotEuclidean
  ∷ hyperbolicLaplacianSpectrumStartsAtOneQuarter
  ∷ euclideanLaplacianSpectrumStartsAtZero
  ∷ hyperbolicYangMillsNotSameAsEuclideanYangMills
  ∷ []

data ShimuraTowerHyperbolicPromotion : Set where

shimuraTowerHyperbolicPromotionImpossibleHere :
  ShimuraTowerHyperbolicPromotion →
  ⊥
shimuraTowerHyperbolicPromotionImpossibleHere ()

poincareMetricStatement :
  String
poincareMetricStatement =
  "Each modular curve X0(N) carries the Poincare metric of constant curvature -1."

productHyperbolicMetricStatement :
  String
productHyperbolicMetricStatement =
  "The product X0(3^k) x X0(4^k) x X0(7^k) carries the product hyperbolic metric."

infiniteTowerHyperbolicStatement :
  String
infiniteTowerHyperbolicStatement =
  "At infinite tower level the dense CM-point spatial geometry is hyperbolic, not Euclidean."

laplacianSpectrumStatement :
  String
laplacianSpectrumStatement =
  "The hyperbolic Laplacian spectrum starts at 1/4, while the Euclidean Laplacian spectrum starts at 0."

yangMillsUniversalityStatement :
  String
yangMillsUniversalityStatement =
  "Hyperbolic Yang-Mills is not the same as Euclidean Yang-Mills; the Shimura-tower Yang-Mills universality class remains open."

record ShimuraTowerHyperbolicGeometryReceipt : Set where
  field
    status :
      ShimuraTowerHyperbolicGeometryStatus

    factors :
      List ShimuraTowerHyperbolicFactor

    factorsAreCanonical :
      factors ≡ canonicalShimuraTowerHyperbolicFactors

    modularCurvesCarryPoincareMetric :
      Bool

    modularCurvesCarryPoincareMetricIsTrue :
      modularCurvesCarryPoincareMetric ≡ true

    poincareMetricCurvature :
      String

    poincareMetricCurvatureIsMinusOne :
      poincareMetricCurvature ≡ "-1"

    productCarriesProductHyperbolicMetric :
      Bool

    productCarriesProductHyperbolicMetricIsTrue :
      productCarriesProductHyperbolicMetric ≡ true

    denseCMPointSpatialGeometryHyperbolic :
      Bool

    denseCMPointSpatialGeometryHyperbolicIsTrue :
      denseCMPointSpatialGeometryHyperbolic ≡ true

    denseCMPointSpatialGeometryEuclidean :
      Bool

    denseCMPointSpatialGeometryEuclideanIsFalse :
      denseCMPointSpatialGeometryEuclidean ≡ false

    hyperbolicLaplacianSpectrumStart :
      String

    hyperbolicLaplacianSpectrumStartIsOneQuarter :
      hyperbolicLaplacianSpectrumStart ≡ "1/4"

    euclideanLaplacianSpectrumStart :
      String

    euclideanLaplacianSpectrumStartIsZero :
      euclideanLaplacianSpectrumStart ≡ "0"

    hyperbolicYangMillsSameAsEuclideanYangMills :
      Bool

    hyperbolicYangMillsSameAsEuclideanYangMillsIsFalse :
      hyperbolicYangMillsSameAsEuclideanYangMills ≡ false

    ymShimuraTowerUniversalityClassOpen :
      Bool

    ymShimuraTowerUniversalityClassOpenIsTrue :
      ymShimuraTowerUniversalityClassOpen ≡ true

    Clay :
      Bool

    ClayIsFalse :
      Clay ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    metricFacts :
      List ShimuraTowerMetricFact

    metricFactsAreCanonical :
      metricFacts ≡ canonicalShimuraTowerMetricFacts

    poincareMetricStatementField :
      String

    poincareMetricStatementIsCanonical :
      poincareMetricStatementField ≡ poincareMetricStatement

    productHyperbolicMetricStatementField :
      String

    productHyperbolicMetricStatementIsCanonical :
      productHyperbolicMetricStatementField ≡ productHyperbolicMetricStatement

    infiniteTowerHyperbolicStatementField :
      String

    infiniteTowerHyperbolicStatementIsCanonical :
      infiniteTowerHyperbolicStatementField ≡ infiniteTowerHyperbolicStatement

    laplacianSpectrumStatementField :
      String

    laplacianSpectrumStatementIsCanonical :
      laplacianSpectrumStatementField ≡ laplacianSpectrumStatement

    yangMillsUniversalityStatementField :
      String

    yangMillsUniversalityStatementIsCanonical :
      yangMillsUniversalityStatementField ≡ yangMillsUniversalityStatement

    promotionFlags :
      List ShimuraTowerHyperbolicPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ShimuraTowerHyperbolicGeometryReceipt public

canonicalShimuraTowerHyperbolicGeometryReceipt :
  ShimuraTowerHyperbolicGeometryReceipt
canonicalShimuraTowerHyperbolicGeometryReceipt =
  record
    { status =
        shimuraTowerHyperbolicGeometryRecordedNoClay
    ; factors =
        canonicalShimuraTowerHyperbolicFactors
    ; factorsAreCanonical =
        refl
    ; modularCurvesCarryPoincareMetric =
        true
    ; modularCurvesCarryPoincareMetricIsTrue =
        refl
    ; poincareMetricCurvature =
        "-1"
    ; poincareMetricCurvatureIsMinusOne =
        refl
    ; productCarriesProductHyperbolicMetric =
        true
    ; productCarriesProductHyperbolicMetricIsTrue =
        refl
    ; denseCMPointSpatialGeometryHyperbolic =
        true
    ; denseCMPointSpatialGeometryHyperbolicIsTrue =
        refl
    ; denseCMPointSpatialGeometryEuclidean =
        false
    ; denseCMPointSpatialGeometryEuclideanIsFalse =
        refl
    ; hyperbolicLaplacianSpectrumStart =
        "1/4"
    ; hyperbolicLaplacianSpectrumStartIsOneQuarter =
        refl
    ; euclideanLaplacianSpectrumStart =
        "0"
    ; euclideanLaplacianSpectrumStartIsZero =
        refl
    ; hyperbolicYangMillsSameAsEuclideanYangMills =
        false
    ; hyperbolicYangMillsSameAsEuclideanYangMillsIsFalse =
        refl
    ; ymShimuraTowerUniversalityClassOpen =
        true
    ; ymShimuraTowerUniversalityClassOpenIsTrue =
        refl
    ; Clay =
        false
    ; ClayIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; metricFacts =
        canonicalShimuraTowerMetricFacts
    ; metricFactsAreCanonical =
        refl
    ; poincareMetricStatementField =
        poincareMetricStatement
    ; poincareMetricStatementIsCanonical =
        refl
    ; productHyperbolicMetricStatementField =
        productHyperbolicMetricStatement
    ; productHyperbolicMetricStatementIsCanonical =
        refl
    ; infiniteTowerHyperbolicStatementField =
        infiniteTowerHyperbolicStatement
    ; infiniteTowerHyperbolicStatementIsCanonical =
        refl
    ; laplacianSpectrumStatementField =
        laplacianSpectrumStatement
    ; laplacianSpectrumStatementIsCanonical =
        refl
    ; yangMillsUniversalityStatementField =
        yangMillsUniversalityStatement
    ; yangMillsUniversalityStatementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "This receipt records hyperbolic Shimura-tower geometry, not Euclidean spatial geometry"
        ∷ "X0(N) is recorded with the Poincare metric of constant curvature -1"
        ∷ "The infinite dense CM-point geometry remains hyperbolic, so hyperbolic Yang-Mills is not identified with Euclidean Yang-Mills"
        ∷ "ymShimuraTowerUniversalityClassOpen is true"
        ∷ "Clay, clayYangMillsPromoted, and terminalClayClaimPromoted remain false"
        ∷ []
    }

shimuraTowerPoincareMetricCurvatureMinusOneReceipt :
  poincareMetricCurvature canonicalShimuraTowerHyperbolicGeometryReceipt
  ≡
  "-1"
shimuraTowerPoincareMetricCurvatureMinusOneReceipt =
  refl

shimuraTowerInfiniteGeometryHyperbolicReceipt :
  denseCMPointSpatialGeometryHyperbolic
    canonicalShimuraTowerHyperbolicGeometryReceipt
  ≡
  true
shimuraTowerInfiniteGeometryHyperbolicReceipt =
  refl

shimuraTowerInfiniteGeometryNotEuclideanReceipt :
  denseCMPointSpatialGeometryEuclidean
    canonicalShimuraTowerHyperbolicGeometryReceipt
  ≡
  false
shimuraTowerInfiniteGeometryNotEuclideanReceipt =
  refl

shimuraTowerHyperbolicLaplacianStartsAtOneQuarterReceipt :
  hyperbolicLaplacianSpectrumStart
    canonicalShimuraTowerHyperbolicGeometryReceipt
  ≡
  "1/4"
shimuraTowerHyperbolicLaplacianStartsAtOneQuarterReceipt =
  refl

shimuraTowerEuclideanLaplacianStartsAtZeroReceipt :
  euclideanLaplacianSpectrumStart
    canonicalShimuraTowerHyperbolicGeometryReceipt
  ≡
  "0"
shimuraTowerEuclideanLaplacianStartsAtZeroReceipt =
  refl

shimuraTowerHyperbolicYMNotEuclideanYMReceipt :
  hyperbolicYangMillsSameAsEuclideanYangMills
    canonicalShimuraTowerHyperbolicGeometryReceipt
  ≡
  false
shimuraTowerHyperbolicYMNotEuclideanYMReceipt =
  refl

ymShimuraTowerUniversalityClassOpenReceipt :
  ymShimuraTowerUniversalityClassOpen
    canonicalShimuraTowerHyperbolicGeometryReceipt
  ≡
  true
ymShimuraTowerUniversalityClassOpenReceipt =
  refl

shimuraTowerHyperbolicGeometryClayFalseReceipt :
  Clay canonicalShimuraTowerHyperbolicGeometryReceipt
  ≡
  false
shimuraTowerHyperbolicGeometryClayFalseReceipt =
  refl

shimuraTowerHyperbolicGeometryClayYangMillsPromotedFalse :
  clayYangMillsPromoted canonicalShimuraTowerHyperbolicGeometryReceipt
  ≡
  false
shimuraTowerHyperbolicGeometryClayYangMillsPromotedFalse =
  refl

shimuraTowerHyperbolicGeometryTerminalClayClaimPromotedFalse :
  terminalClayClaimPromoted canonicalShimuraTowerHyperbolicGeometryReceipt
  ≡
  false
shimuraTowerHyperbolicGeometryTerminalClayClaimPromotedFalse =
  refl
