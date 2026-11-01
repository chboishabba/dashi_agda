module DASHI.Physics.Closure.YMCuspMetricExpansionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yang-Mills cusp metric expansion receipt.
--
-- This receipt records the local cusp-coordinate expansion near a cusp of
-- X_0(N).  With q = exp(2*pi*i*tau/N), the metric in the q-coordinate is
-- recorded as g_{mu nu} = delta_{mu nu}(1 + O(|q|^2)).  As N -> infinity,
-- the cusp region {|q| < epsilon} grows while the O(|q|^2) correction remains
-- small on that region.  The Yang-Mills action is therefore recorded as the
-- flat action with an O(|q|^2) cusp correction:
-- S = 1/(2g^2) integral Tr |F|^2 sqrt(g) d4x = S_flat(1 + O(|q|^2)).

data YMCuspMetricExpansionStatus : Set where
  cuspMetricExpansionRecorded :
    YMCuspMetricExpansionStatus

data CuspMetricExpansion : Set where
  flatPlusOqSquared :
    CuspMetricExpansion

data YMCuspMetricExpansionFact : Set where
  cuspOfX0N :
    YMCuspMetricExpansionFact

  qCoordinateExpTwoPiITauOverN :
    YMCuspMetricExpansionFact

  metricFlatPlusOqSquaredInQCoordinate :
    YMCuspMetricExpansionFact

  cuspRegionQNormLessThanEpsilon :
    YMCuspMetricExpansionFact

  cuspRegionGrowsAsNTendsToInfinity :
    YMCuspMetricExpansionFact

  oqSquaredMetricCorrectionRemainsSmall :
    YMCuspMetricExpansionFact

  ymActionFlatPlusOqSquaredCorrection :
    YMCuspMetricExpansionFact

canonicalYMCuspMetricExpansionFacts :
  List YMCuspMetricExpansionFact
canonicalYMCuspMetricExpansionFacts =
  cuspOfX0N
  ∷ qCoordinateExpTwoPiITauOverN
  ∷ metricFlatPlusOqSquaredInQCoordinate
  ∷ cuspRegionQNormLessThanEpsilon
  ∷ cuspRegionGrowsAsNTendsToInfinity
  ∷ oqSquaredMetricCorrectionRemainsSmall
  ∷ ymActionFlatPlusOqSquaredCorrection
  ∷ []

cuspMetricExpansionStatement :
  String
cuspMetricExpansionStatement =
  "Near a cusp of X_0(N), with q = exp(2*pi*i*tau/N), the q-coordinate metric is g_{mu nu}=delta_{mu nu}(1+O(|q|^2))."

cuspRegionGrowthStatement :
  String
cuspRegionGrowthStatement =
  "As N -> infinity, the cusp region {|q|<epsilon} grows while the O(|q|^2) metric correction remains small."

ymActionCuspExpansionStatement :
  String
ymActionCuspExpansionStatement =
  "S = 1/(2g^2) integral Tr |F|^2 sqrt(g) d4x = S_flat(1+O(|q|^2))."

record YMCuspMetricExpansionReceipt : Setω where
  field
    status :
      YMCuspMetricExpansionStatus

    statusIsCanonical :
      status ≡ cuspMetricExpansionRecorded

    modularCurve :
      String

    modularCurveIsX0N :
      modularCurve ≡ "X_0(N)"

    cusp :
      String

    cuspIsCuspOfX0N :
      cusp ≡ "cusp of X_0(N)"

    qCoordinate :
      String

    qCoordinateIsCanonical :
      qCoordinate ≡ "q = exp(2*pi*i*tau/N)"

    metricFormula :
      String

    metricFormulaIsCanonical :
      metricFormula ≡ "g_{mu nu}=delta_{mu nu}(1+O(|q|^2))"

    cuspMetricExpansion :
      CuspMetricExpansion

    cuspMetricExpansionIsFlatPlusOqSquared :
      cuspMetricExpansion ≡ flatPlusOqSquared

    cuspRegion :
      String

    cuspRegionIsSmallQDisk :
      cuspRegion ≡ "{|q|<epsilon}"

    cuspRegionGrowsWithN :
      Bool

    cuspRegionGrowsWithNIsTrue :
      cuspRegionGrowsWithN ≡ true

    oqSquaredCorrectionRemainsSmall :
      Bool

    oqSquaredCorrectionRemainsSmallIsTrue :
      oqSquaredCorrectionRemainsSmall ≡ true

    ymActionFormula :
      String

    ymActionFormulaIsCanonical :
      ymActionFormula ≡ "S = 1/(2g^2) integral Tr |F|^2 sqrt(g) d4x"

    ymActionCuspExpansion :
      String

    ymActionCuspExpansionIsCanonical :
      ymActionCuspExpansion ≡ "S_flat(1+O(|q|^2))"

    ymActionCuspCorrectionOrderQ2 :
      Bool

    ymActionCuspCorrectionOrderQ2IsTrue :
      ymActionCuspCorrectionOrderQ2 ≡ true

    facts :
      List YMCuspMetricExpansionFact

    factsAreCanonical :
      facts ≡ canonicalYMCuspMetricExpansionFacts

    metricStatement :
      String

    metricStatementIsCanonical :
      metricStatement ≡ cuspMetricExpansionStatement

    regionStatement :
      String

    regionStatementIsCanonical :
      regionStatement ≡ cuspRegionGrowthStatement

    actionStatement :
      String

    actionStatementIsCanonical :
      actionStatement ≡ ymActionCuspExpansionStatement

    receiptBoundary :
      List String

open YMCuspMetricExpansionReceipt public

canonicalYMCuspMetricExpansionReceipt :
  YMCuspMetricExpansionReceipt
canonicalYMCuspMetricExpansionReceipt =
  record
    { status =
        cuspMetricExpansionRecorded
    ; statusIsCanonical =
        refl
    ; modularCurve =
        "X_0(N)"
    ; modularCurveIsX0N =
        refl
    ; cusp =
        "cusp of X_0(N)"
    ; cuspIsCuspOfX0N =
        refl
    ; qCoordinate =
        "q = exp(2*pi*i*tau/N)"
    ; qCoordinateIsCanonical =
        refl
    ; metricFormula =
        "g_{mu nu}=delta_{mu nu}(1+O(|q|^2))"
    ; metricFormulaIsCanonical =
        refl
    ; cuspMetricExpansion =
        flatPlusOqSquared
    ; cuspMetricExpansionIsFlatPlusOqSquared =
        refl
    ; cuspRegion =
        "{|q|<epsilon}"
    ; cuspRegionIsSmallQDisk =
        refl
    ; cuspRegionGrowsWithN =
        true
    ; cuspRegionGrowsWithNIsTrue =
        refl
    ; oqSquaredCorrectionRemainsSmall =
        true
    ; oqSquaredCorrectionRemainsSmallIsTrue =
        refl
    ; ymActionFormula =
        "S = 1/(2g^2) integral Tr |F|^2 sqrt(g) d4x"
    ; ymActionFormulaIsCanonical =
        refl
    ; ymActionCuspExpansion =
        "S_flat(1+O(|q|^2))"
    ; ymActionCuspExpansionIsCanonical =
        refl
    ; ymActionCuspCorrectionOrderQ2 =
        true
    ; ymActionCuspCorrectionOrderQ2IsTrue =
        refl
    ; facts =
        canonicalYMCuspMetricExpansionFacts
    ; factsAreCanonical =
        refl
    ; metricStatement =
        cuspMetricExpansionStatement
    ; metricStatementIsCanonical =
        refl
    ; regionStatement =
        cuspRegionGrowthStatement
    ; regionStatementIsCanonical =
        refl
    ; actionStatement =
        ymActionCuspExpansionStatement
    ; actionStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Records the q-coordinate cusp metric expansion g_{mu nu}=delta_{mu nu}(1+O(|q|^2)) near a cusp of X_0(N)"
        ∷ "Records that the cusp region {|q|<epsilon} grows as N -> infinity while the O(|q|^2) correction remains small"
        ∷ "Records the Yang-Mills action as S_flat(1+O(|q|^2)) in the cusp region"
        ∷ []
    }

cuspMetricExpansionFlagIsFlatPlusOqSquared :
  cuspMetricExpansion canonicalYMCuspMetricExpansionReceipt ≡ flatPlusOqSquared
cuspMetricExpansionFlagIsFlatPlusOqSquared =
  refl

cuspRegionGrowsWithNFlagIsTrue :
  cuspRegionGrowsWithN canonicalYMCuspMetricExpansionReceipt ≡ true
cuspRegionGrowsWithNFlagIsTrue =
  refl

ymActionCuspCorrectionOrderQ2FlagIsTrue :
  ymActionCuspCorrectionOrderQ2 canonicalYMCuspMetricExpansionReceipt ≡ true
ymActionCuspCorrectionOrderQ2FlagIsTrue =
  refl
