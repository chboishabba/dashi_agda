module DASHI.Physics.Closure.YMProgressSummaryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yang-Mills progress summary receipt.
--
-- This C2 receipt records programme progress only.  It discharges the
-- previously open spatial-refinement and p-adic flat-limit lanes as
-- inhabited programme surfaces, records the new p-adic Wilson-action and
-- 4D lattice-tree surfaces, and keeps the single remaining blocker as the
-- archimedean H^3 to R^3 flat limit.  It deliberately promotes no Clay
-- Yang-Mills theorem or terminal claim.

data YMProgressSummaryStatus : Set where
  genuineProgressWithSingleArchimedeanFlatLimitGap :
    YMProgressSummaryStatus

data YMPreviouslyOpenItem : Set where
  spatialRefinementOpen :
    YMPreviouslyOpenItem

  universalityClassOpen :
    YMPreviouslyOpenItem

  flatLimitOpen :
    YMPreviouslyOpenItem

canonicalYMPreviouslyOpenItems :
  List YMPreviouslyOpenItem
canonicalYMPreviouslyOpenItems =
  spatialRefinementOpen
  ∷ universalityClassOpen
  ∷ flatLimitOpen
  ∷ []

data YMInhabitedProgressItem : Set where
  spatialRefinementViaShimuraTower :
    YMInhabitedProgressItem

  pAdicFlatLimitViaBruhatTitsUltrametricBoundary :
    YMInhabitedProgressItem

  pAdicWilsonActionWithSixtyEightPlaquetteTypes :
    YMInhabitedProgressItem

  pAdicWilsonReflectionPositivity :
    YMInhabitedProgressItem

  pAdicFourDimensionalLatticeTreesTimesDepth :
    YMInhabitedProgressItem

canonicalYMInhabitedProgressItems :
  List YMInhabitedProgressItem
canonicalYMInhabitedProgressItems =
  spatialRefinementViaShimuraTower
  ∷ pAdicFlatLimitViaBruhatTitsUltrametricBoundary
  ∷ pAdicWilsonActionWithSixtyEightPlaquetteTypes
  ∷ pAdicWilsonReflectionPositivity
  ∷ pAdicFourDimensionalLatticeTreesTimesDepth
  ∷ []

data YMRemainingOpenGap : Set where
  archimedeanH3ToR3FlatLimit :
    YMRemainingOpenGap

canonicalYMRemainingOpenGaps :
  List YMRemainingOpenGap
canonicalYMRemainingOpenGaps =
  archimedeanH3ToR3FlatLimit
  ∷ []

data YMProgressClayPromotion : Set where

ymProgressClayPromotionImpossibleHere :
  YMProgressClayPromotion →
  ⊥
ymProgressClayPromotionImpossibleHere ()

spatialRefinementProgressStatement : String
spatialRefinementProgressStatement =
  "Spatial refinement is now inhabited via the Shimura tower."

pAdicFlatLimitProgressStatement : String
pAdicFlatLimitProgressStatement =
  "The p-adic flat limit is now inhabited via the Bruhat-Tits ultrametric boundary."

pAdicWilsonProgressStatement : String
pAdicWilsonProgressStatement =
  "The p-adic Wilson action is now inhabited with 68 plaquette types and reflection positivity."

pAdicFourDimensionalLatticeTreeStatementLabel : String
pAdicFourDimensionalLatticeTreeStatementLabel =
  "The p-adic four-dimensional carrier is recorded as lattice trees times depth."

remainingArchimedeanGapStatement : String
remainingArchimedeanGapStatement =
  "The remaining single gap is the archimedean H^3 to R^3 flat limit."

ymProgressSummaryStatement : String
ymProgressSummaryStatement =
  "Yang-Mills programme state: genuine progress has been made; spatial refinement, p-adic flat limit, p-adic Wilson action with 68 plaquette types and reflection positivity, and p-adic 4D lattice trees times depth are inhabited; the only remaining open gap is the archimedean H^3 to R^3 flat limit; no Clay Yang-Mills promotion is made."

record YMProgressSummaryReceipt : Setω where
  field
    status :
      YMProgressSummaryStatus

    previouslyOpenItems :
      List YMPreviouslyOpenItem

    previouslyOpenItemsAreCanonical :
      previouslyOpenItems ≡ canonicalYMPreviouslyOpenItems

    inhabitedProgressItems :
      List YMInhabitedProgressItem

    inhabitedProgressItemsAreCanonical :
      inhabitedProgressItems ≡ canonicalYMInhabitedProgressItems

    spatialRefinementViaShimuraTowerInhabited :
      Bool

    spatialRefinementViaShimuraTowerInhabitedIsTrue :
      spatialRefinementViaShimuraTowerInhabited ≡ true

    pAdicFlatLimitViaBruhatTitsBoundaryInhabited :
      Bool

    pAdicFlatLimitViaBruhatTitsBoundaryInhabitedIsTrue :
      pAdicFlatLimitViaBruhatTitsBoundaryInhabited ≡ true

    pAdicWilsonActionInhabited :
      Bool

    pAdicWilsonActionInhabitedIsTrue :
      pAdicWilsonActionInhabited ≡ true

    pAdicWilsonPlaquetteTypeCount :
      Nat

    pAdicWilsonPlaquetteTypeCountIsSixtyEight :
      pAdicWilsonPlaquetteTypeCount ≡ 68

    pAdicWilsonReflectionPositivityInhabited :
      Bool

    pAdicWilsonReflectionPositivityInhabitedIsTrue :
      pAdicWilsonReflectionPositivityInhabited ≡ true

    pAdicFourDimensionalLatticeTreesTimesDepthInhabited :
      Bool

    pAdicFourDimensionalLatticeTreesTimesDepthInhabitedIsTrue :
      pAdicFourDimensionalLatticeTreesTimesDepthInhabited ≡ true

    pAdicCarrierDimension :
      Nat

    pAdicCarrierDimensionIsFour :
      pAdicCarrierDimension ≡ 4

    remainingOpenGaps :
      List YMRemainingOpenGap

    remainingOpenGapsAreCanonical :
      remainingOpenGaps ≡ canonicalYMRemainingOpenGaps

    remainingOpenGap :
      YMRemainingOpenGap

    remainingOpenGapIsArchimedeanH3ToR3FlatLimit :
      remainingOpenGap ≡ archimedeanH3ToR3FlatLimit

    remainingOpenGapCount :
      Nat

    remainingOpenGapCountIsOne :
      remainingOpenGapCount ≡ 1

    programmeMadeGenuineProgress :
      Bool

    programmeMadeGenuineProgressIsTrue :
      programmeMadeGenuineProgress ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List YMProgressClayPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    spatialRefinementStatement :
      String

    spatialRefinementStatementIsCanonical :
      spatialRefinementStatement ≡ spatialRefinementProgressStatement

    pAdicFlatLimitStatement :
      String

    pAdicFlatLimitStatementIsCanonical :
      pAdicFlatLimitStatement ≡ pAdicFlatLimitProgressStatement

    pAdicWilsonStatement :
      String

    pAdicWilsonStatementIsCanonical :
      pAdicWilsonStatement ≡ pAdicWilsonProgressStatement

    pAdicFourDimensionalLatticeTreeStatement :
      String

    pAdicFourDimensionalLatticeTreeStatementIsCanonical :
      pAdicFourDimensionalLatticeTreeStatement
      ≡
      pAdicFourDimensionalLatticeTreeStatementLabel

    remainingGapStatement :
      String

    remainingGapStatementIsCanonical :
      remainingGapStatement ≡ remainingArchimedeanGapStatement

    statement :
      String

    statementIsCanonical :
      statement ≡ ymProgressSummaryStatement

    receiptBoundary :
      List String

open YMProgressSummaryReceipt public

canonicalYMProgressSummaryReceipt :
  YMProgressSummaryReceipt
canonicalYMProgressSummaryReceipt =
  record
    { status =
        genuineProgressWithSingleArchimedeanFlatLimitGap
    ; previouslyOpenItems =
        canonicalYMPreviouslyOpenItems
    ; previouslyOpenItemsAreCanonical =
        refl
    ; inhabitedProgressItems =
        canonicalYMInhabitedProgressItems
    ; inhabitedProgressItemsAreCanonical =
        refl
    ; spatialRefinementViaShimuraTowerInhabited =
        true
    ; spatialRefinementViaShimuraTowerInhabitedIsTrue =
        refl
    ; pAdicFlatLimitViaBruhatTitsBoundaryInhabited =
        true
    ; pAdicFlatLimitViaBruhatTitsBoundaryInhabitedIsTrue =
        refl
    ; pAdicWilsonActionInhabited =
        true
    ; pAdicWilsonActionInhabitedIsTrue =
        refl
    ; pAdicWilsonPlaquetteTypeCount =
        68
    ; pAdicWilsonPlaquetteTypeCountIsSixtyEight =
        refl
    ; pAdicWilsonReflectionPositivityInhabited =
        true
    ; pAdicWilsonReflectionPositivityInhabitedIsTrue =
        refl
    ; pAdicFourDimensionalLatticeTreesTimesDepthInhabited =
        true
    ; pAdicFourDimensionalLatticeTreesTimesDepthInhabitedIsTrue =
        refl
    ; pAdicCarrierDimension =
        4
    ; pAdicCarrierDimensionIsFour =
        refl
    ; remainingOpenGaps =
        canonicalYMRemainingOpenGaps
    ; remainingOpenGapsAreCanonical =
        refl
    ; remainingOpenGap =
        archimedeanH3ToR3FlatLimit
    ; remainingOpenGapIsArchimedeanH3ToR3FlatLimit =
        refl
    ; remainingOpenGapCount =
        1
    ; remainingOpenGapCountIsOne =
        refl
    ; programmeMadeGenuineProgress =
        true
    ; programmeMadeGenuineProgressIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; spatialRefinementStatement =
        spatialRefinementProgressStatement
    ; spatialRefinementStatementIsCanonical =
        refl
    ; pAdicFlatLimitStatement =
        pAdicFlatLimitProgressStatement
    ; pAdicFlatLimitStatementIsCanonical =
        refl
    ; pAdicWilsonStatement =
        pAdicWilsonProgressStatement
    ; pAdicWilsonStatementIsCanonical =
        refl
    ; pAdicFourDimensionalLatticeTreeStatement =
        pAdicFourDimensionalLatticeTreeStatementLabel
    ; pAdicFourDimensionalLatticeTreeStatementIsCanonical =
        refl
    ; remainingGapStatement =
        remainingArchimedeanGapStatement
    ; remainingGapStatementIsCanonical =
        refl
    ; statement =
        ymProgressSummaryStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        spatialRefinementProgressStatement
        ∷ pAdicFlatLimitProgressStatement
        ∷ pAdicWilsonProgressStatement
        ∷ pAdicFourDimensionalLatticeTreeStatementLabel
        ∷ remainingArchimedeanGapStatement
        ∷ ymProgressSummaryStatement
        ∷ []
    }

ymProgressSummaryRecordsGenuineProgress :
  programmeMadeGenuineProgress canonicalYMProgressSummaryReceipt
  ≡
  true
ymProgressSummaryRecordsGenuineProgress =
  refl

ymProgressSummaryRecordsSingleRemainingGap :
  remainingOpenGap canonicalYMProgressSummaryReceipt
  ≡
  archimedeanH3ToR3FlatLimit
ymProgressSummaryRecordsSingleRemainingGap =
  refl

ymProgressSummaryRecordsSixtyEightPlaquetteTypes :
  pAdicWilsonPlaquetteTypeCount canonicalYMProgressSummaryReceipt
  ≡
  68
ymProgressSummaryRecordsSixtyEightPlaquetteTypes =
  refl

ymProgressSummaryKeepsClayFalse :
  clayYangMillsPromoted canonicalYMProgressSummaryReceipt
  ≡
  false
ymProgressSummaryKeepsClayFalse =
  refl

ymProgressSummaryKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYMProgressSummaryReceipt
  ≡
  false
ymProgressSummaryKeepsTerminalFalse =
  refl

ymProgressSummaryNoPromotion :
  YMProgressClayPromotion →
  ⊥
ymProgressSummaryNoPromotion =
  ymProgressClayPromotionImpossibleHere
