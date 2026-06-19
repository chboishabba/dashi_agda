module DASHI.Physics.Closure.Lambda2PlusTransportInequalityBoundaryHBReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Post-Calc-11 receipt surface for the lambda2plus transport inequality
-- and the BoundaryHB corrected closeability ledger.
--
-- The transport side records the standard/write-now lambda2plus_transport_ineq
-- shape with nu, C_NS, t1, t2, lambda2+, L2, and L3 tokens.  The
-- BoundaryHB side records the corrected route: BoundaryHB_Correct closes
-- only through the pointwise route lambda2 = 0, lambda1 = -lambda3,
-- lambda3 >= lambda_min, and pointwise ||nabla^2 u|| >= eta, which
-- projects to max_k B_k >= b0 through pointwise kornBiaxialBound, with
-- the Kato second-derivative formula recording B_k =
-- 2 lambda3^2 |<partial_k e1, e2>|^2 on the biaxial boundary and the
-- pointwise lower bound recorded as b0.
-- Integral Korn plus continuity is explicitly insufficient, KornLevelSet
-- remains open for h_strain_dom, and no Clay promotion is claimed here.

data Lambda2PlusTransportInequalityStatus : Set where
  lambda2PlusTransportShapeRecordedStandardWriteNow :
    Lambda2PlusTransportInequalityStatus

data Lambda2PlusTransportInequalityToken : Set where
  nuToken :
    Lambda2PlusTransportInequalityToken

  cNSToken :
    Lambda2PlusTransportInequalityToken

  t1Token :
    Lambda2PlusTransportInequalityToken

  t2Token :
    Lambda2PlusTransportInequalityToken

  lambda2PlusToken :
    Lambda2PlusTransportInequalityToken

  l2Token :
    Lambda2PlusTransportInequalityToken

  l3Token :
    Lambda2PlusTransportInequalityToken

canonicalLambda2PlusTransportInequalityTokens :
  List Lambda2PlusTransportInequalityToken
canonicalLambda2PlusTransportInequalityTokens =
  nuToken
  ∷ cNSToken
  ∷ t1Token
  ∷ t2Token
  ∷ lambda2PlusToken
  ∷ l2Token
  ∷ l3Token
  ∷ []

data Lambda2PlusTransportInequalityPromotion : Set where

lambda2PlusTransportInequalityPromotionImpossibleHere :
  Lambda2PlusTransportInequalityPromotion →
  ⊥
lambda2PlusTransportInequalityPromotionImpossibleHere ()

lambda2PlusTransportInequalityStatement : String
lambda2PlusTransportInequalityStatement =
  "standard/write-now transport inequality shape: nu, C_NS, t1, t2, lambda2+, L2, and L3 terms are recorded, and no theorem promotion is claimed"

data BoundaryHBAssemblyStatus : Set where
  boundaryHBCorrectPointwiseRouteRecordedCandidateOnly :
    BoundaryHBAssemblyStatus

data BoundaryHBAssemblyBlocker : Set where
  integralKornPlusContinuityInsufficient :
    BoundaryHBAssemblyBlocker

  continuityDoesNotUpgradeIntegralToPointwise :
    BoundaryHBAssemblyBlocker

  missingPointwiseKornBiaxialBound :
    BoundaryHBAssemblyBlocker

  missingBiaxialBoundaryHypothesis :
    BoundaryHBAssemblyBlocker

  missingLambda3GapHypothesis :
    BoundaryHBAssemblyBlocker

  missingPointwiseNabla2ULowerBoundEta :
    BoundaryHBAssemblyBlocker

  kornLevelSetOpenForHStrainDom :
    BoundaryHBAssemblyBlocker

data BoundaryHBPointwiseRouteProjection : Set where
  lambda2EqualsZeroProjected :
    BoundaryHBPointwiseRouteProjection

  lambda1EqualsNegativeLambda3Projected :
    BoundaryHBPointwiseRouteProjection

  lambda3AtLeastLambdaMinProjected :
    BoundaryHBPointwiseRouteProjection

  pointwiseNabla2ULowerBoundEtaProjected :
    BoundaryHBPointwiseRouteProjection

  pointwiseMaxBKAtLeastB0Projected :
    BoundaryHBPointwiseRouteProjection

data BoundaryHBPointwiseRouteStep : Set where
  biaxialBoundaryLambda2ZeroAndLambda1NegativeLambda3Recorded :
    BoundaryHBPointwiseRouteStep

  katoSecondDerivativeFormulaRecorded :
    BoundaryHBPointwiseRouteStep

  lambda3AtLeastLambdaMinRecorded :
    BoundaryHBPointwiseRouteStep

  pointwiseNabla2ULowerBoundEtaRecorded :
    BoundaryHBPointwiseRouteStep

  pointwiseKornBiaxialBoundRecorded :
    BoundaryHBPointwiseRouteStep

  pointwiseMaxBKAtLeastB0Recorded :
    BoundaryHBPointwiseRouteStep

canonicalBoundaryHBPointwiseRouteSteps :
  List BoundaryHBPointwiseRouteStep
canonicalBoundaryHBPointwiseRouteSteps =
  biaxialBoundaryLambda2ZeroAndLambda1NegativeLambda3Recorded
  ∷ katoSecondDerivativeFormulaRecorded
  ∷ lambda3AtLeastLambdaMinRecorded
  ∷ pointwiseNabla2ULowerBoundEtaRecorded
  ∷ pointwiseKornBiaxialBoundRecorded
  ∷ pointwiseMaxBKAtLeastB0Recorded
  ∷ []

boundaryHBPointwiseKatoFormulaStatement : String
boundaryHBPointwiseKatoFormulaStatement =
  "On the biaxial boundary, lambda2 = 0 and lambda1 = -lambda3; Kato's second-derivative formula gives B_k = 2 lambda3^2 |<partial_k e1, e2>|^2."

boundaryHBPointwiseB0Statement : String
boundaryHBPointwiseB0Statement =
  "With lambda3 >= lambda_min and ||nabla^2 u||_F >= eta, pointwise kornBiaxialBound yields max_k B_k >= (2/3) * lambda_min^2 * eta^2 / const, recorded as b0."

boundaryHBPointwiseRouteStatement : String
boundaryHBPointwiseRouteStatement =
  "BoundaryHB_Correct pointwise route: on the biaxial boundary lambda2 = 0 and lambda1 = -lambda3; Kato's second-derivative formula gives B_k = 2 lambda3^2 |<partial_k e1, e2>|^2; with lambda3 >= lambda_min and ||nabla^2 u||_F >= eta, pointwise kornBiaxialBound yields max_k B_k >= b0."

canonicalBoundaryHBPointwiseRouteProjection :
  List BoundaryHBPointwiseRouteProjection
canonicalBoundaryHBPointwiseRouteProjection =
  lambda2EqualsZeroProjected
  ∷ lambda1EqualsNegativeLambda3Projected
  ∷ lambda3AtLeastLambdaMinProjected
  ∷ pointwiseNabla2ULowerBoundEtaProjected
  ∷ pointwiseMaxBKAtLeastB0Projected
  ∷ []

boundaryHBPointwiseRouteProjectionStatement : String
boundaryHBPointwiseRouteProjectionStatement =
  "BoundaryHB_Correct pointwise route: lambda2 = 0, lambda1 = -lambda3, lambda3 >= lambda_min, and ||nabla^2 u|| >= eta project to max_k B_k >= b0."

record BoundaryHBPointwiseRouteReceipt : Set where
  field
    status :
      BoundaryHBAssemblyStatus

    statusIsCanonical :
      status ≡ boundaryHBCorrectPointwiseRouteRecordedCandidateOnly

    routeSteps :
      List BoundaryHBPointwiseRouteStep

    routeStepsAreCanonical :
      routeSteps ≡ canonicalBoundaryHBPointwiseRouteSteps

    routeProjection :
      List BoundaryHBPointwiseRouteProjection

    routeProjectionIsCanonical :
      routeProjection ≡ canonicalBoundaryHBPointwiseRouteProjection

    biaxialBoundaryLambda2ZeroAndLambda1NegativeLambda3 :
      Bool

    biaxialBoundaryLambda2ZeroAndLambda1NegativeLambda3IsTrue :
      biaxialBoundaryLambda2ZeroAndLambda1NegativeLambda3 ≡ true

    katoSecondDerivativeFormula :
      Bool

    katoSecondDerivativeFormulaIsTrue :
      katoSecondDerivativeFormula ≡ true

    katoSecondDerivativeFormulaStatement :
      String

    katoSecondDerivativeFormulaStatementIsCanonical :
      katoSecondDerivativeFormulaStatement ≡ boundaryHBPointwiseKatoFormulaStatement

    lambda3AtLeastLambdaMin :
      Bool

    lambda3AtLeastLambdaMinIsTrue :
      lambda3AtLeastLambdaMin ≡ true

    pointwiseNabla2ULowerBoundEta :
      Bool

    pointwiseNabla2ULowerBoundEtaIsTrue :
      pointwiseNabla2ULowerBoundEta ≡ true

    pointwiseKornBiaxialBound :
      Bool

    pointwiseKornBiaxialBoundIsTrue :
      pointwiseKornBiaxialBound ≡ true

    pointwiseMaxBKAtLeastB0 :
      Bool

    pointwiseMaxBKAtLeastB0IsTrue :
      pointwiseMaxBKAtLeastB0 ≡ true

    b0Recorded :
      Bool

    b0RecordedIsTrue :
      b0Recorded ≡ true

    b0RecordedStatement :
      String

    b0RecordedStatementIsCanonical :
      b0RecordedStatement ≡ boundaryHBPointwiseB0Statement

    integralKornPlusContinuityInsufficientRouteFlag :
      Bool

    integralKornPlusContinuityInsufficientRouteFlagIsTrue :
      integralKornPlusContinuityInsufficientRouteFlag ≡ true

    kornLevelSetRemainsOpen :
      Bool

    kornLevelSetRemainsOpenIsTrue :
      kornLevelSetRemainsOpen ≡ true

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    routeStatement :
      String

    routeStatementIsCanonical :
      routeStatement ≡ boundaryHBPointwiseRouteStatement

    receiptBoundary :
      List String

open BoundaryHBPointwiseRouteReceipt public

canonicalBoundaryHBPointwiseRouteReceipt :
  BoundaryHBPointwiseRouteReceipt
canonicalBoundaryHBPointwiseRouteReceipt =
  record
    { status =
        boundaryHBCorrectPointwiseRouteRecordedCandidateOnly
    ; statusIsCanonical =
        refl
    ; routeSteps =
        canonicalBoundaryHBPointwiseRouteSteps
    ; routeStepsAreCanonical =
        refl
    ; routeProjection =
        canonicalBoundaryHBPointwiseRouteProjection
    ; routeProjectionIsCanonical =
        refl
    ; biaxialBoundaryLambda2ZeroAndLambda1NegativeLambda3 =
        true
    ; biaxialBoundaryLambda2ZeroAndLambda1NegativeLambda3IsTrue =
        refl
    ; katoSecondDerivativeFormula =
        true
    ; katoSecondDerivativeFormulaIsTrue =
        refl
    ; katoSecondDerivativeFormulaStatement =
        boundaryHBPointwiseKatoFormulaStatement
    ; katoSecondDerivativeFormulaStatementIsCanonical =
        refl
    ; lambda3AtLeastLambdaMin =
        true
    ; lambda3AtLeastLambdaMinIsTrue =
        refl
    ; pointwiseNabla2ULowerBoundEta =
        true
    ; pointwiseNabla2ULowerBoundEtaIsTrue =
        refl
    ; pointwiseKornBiaxialBound =
        true
    ; pointwiseKornBiaxialBoundIsTrue =
        refl
    ; pointwiseMaxBKAtLeastB0 =
        true
    ; pointwiseMaxBKAtLeastB0IsTrue =
        refl
    ; b0Recorded =
        true
    ; b0RecordedIsTrue =
        refl
    ; b0RecordedStatement =
        boundaryHBPointwiseB0Statement
    ; b0RecordedStatementIsCanonical =
        refl
    ; integralKornPlusContinuityInsufficientRouteFlag =
        true
    ; integralKornPlusContinuityInsufficientRouteFlagIsTrue =
        refl
    ; kornLevelSetRemainsOpen =
        true
    ; kornLevelSetRemainsOpenIsTrue =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; routeStatement =
        boundaryHBPointwiseRouteStatement
    ; routeStatementIsCanonical =
        refl
    ; receiptBoundary =
        "BoundaryHB_Correct pointwise route recorded on the biaxial boundary"
        ∷ "lambda2 = 0 and lambda1 = -lambda3 are recorded explicitly"
        ∷ "Kato second-derivative formula records B_k = 2 lambda3^2 |<partial_k e1, e2>|^2"
        ∷ "lambda3 >= lambda_min and ||nabla^2 u||_F >= eta feed pointwise kornBiaxialBound"
        ∷ "The resulting max_k B_k lower bound is recorded as b0"
        ∷ "Integral Korn plus continuity is explicitly insufficient"
        ∷ "KornLevelSet remains open for h_strain_dom"
        ∷ "Clay promotion stays false"
        ∷ []
    }

canonicalBoundaryHBAssemblyBlockers :
  List BoundaryHBAssemblyBlocker
canonicalBoundaryHBAssemblyBlockers =
  integralKornPlusContinuityInsufficient
  ∷ continuityDoesNotUpgradeIntegralToPointwise
  ∷ missingPointwiseKornBiaxialBound
  ∷ missingBiaxialBoundaryHypothesis
  ∷ missingLambda3GapHypothesis
  ∷ missingPointwiseNabla2ULowerBoundEta
  ∷ kornLevelSetOpenForHStrainDom
  ∷ []

data BoundaryHBAssemblyPromotion : Set where

boundaryHBAssemblyPromotionImpossibleHere :
  BoundaryHBAssemblyPromotion →
  ⊥
boundaryHBAssemblyPromotionImpossibleHere ()

boundaryHBAssemblyStatementText : String
boundaryHBAssemblyStatementText =
  "BoundaryHB_Correct is closeable only through pointwise kornBiaxialBound under the pointwise route lambda2 = 0, lambda1 = -lambda3, lambda3 >= lambda_min, and pointwise ||nabla^2 u|| >= eta, with max_k B_k >= b0 recorded as the consequence; integral Korn plus continuity is explicitly insufficient; KornLevelSet remains open for h_strain_dom; Clay promotion stays false."

record Lambda2PlusTransportInequalityReceipt : Setω where
  field
    status :
      Lambda2PlusTransportInequalityStatus

    statusIsCanonical :
      status ≡ lambda2PlusTransportShapeRecordedStandardWriteNow

    tokens :
      List Lambda2PlusTransportInequalityToken

    tokensAreCanonical :
      tokens ≡ canonicalLambda2PlusTransportInequalityTokens

    transportInequalityStatement :
      String

    transportInequalityStatementIsCanonical :
      transportInequalityStatement ≡ lambda2PlusTransportInequalityStatement

    standardWriteNow :
      Bool

    standardWriteNowIsTrue :
      standardWriteNow ≡ true

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    promotionFlags :
      List Lambda2PlusTransportInequalityPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

record BoundaryHBAssemblyReceipt : Setω where
  field
    status :
      BoundaryHBAssemblyStatus

    statusIsCanonical :
      status ≡ boundaryHBCorrectPointwiseRouteRecordedCandidateOnly

    blockers :
      List BoundaryHBAssemblyBlocker

    blockersAreCanonical :
      blockers ≡ canonicalBoundaryHBAssemblyBlockers

    pointwiseKornBiaxialBoundRequired :
      Bool

    pointwiseKornBiaxialBoundRequiredIsTrue :
      pointwiseKornBiaxialBoundRequired ≡ true

    lambda2ZeroRequired :
      Bool

    lambda2ZeroRequiredIsTrue :
      lambda2ZeroRequired ≡ true

    lambda1EqualsNegativeLambda3Required :
      Bool

    lambda1EqualsNegativeLambda3RequiredIsTrue :
      lambda1EqualsNegativeLambda3Required ≡ true

    lambda3AtLeastLambdaMinRequired :
      Bool

    lambda3AtLeastLambdaMinRequiredIsTrue :
      lambda3AtLeastLambdaMinRequired ≡ true

    biaxialBoundaryRequired :
      Bool

    biaxialBoundaryRequiredIsTrue :
      biaxialBoundaryRequired ≡ true

    lambda3GapRequired :
      Bool

    lambda3GapRequiredIsTrue :
      lambda3GapRequired ≡ true

    pointwiseNabla2ULowerBoundEtaRequired :
      Bool

    pointwiseNabla2ULowerBoundEtaRequiredIsTrue :
      pointwiseNabla2ULowerBoundEtaRequired ≡ true

    pointwiseMaxBKAtLeastB0Required :
      Bool

    pointwiseMaxBKAtLeastB0RequiredIsTrue :
      pointwiseMaxBKAtLeastB0Required ≡ true

    integralKornPlusContinuityInsufficientFlag :
      Bool

    integralKornPlusContinuityInsufficientFlagIsTrue :
      integralKornPlusContinuityInsufficientFlag ≡ true

    kornLevelSetOpenForHStrainDomFlag :
      Bool

    kornLevelSetOpenForHStrainDomFlagIsTrue :
      kornLevelSetOpenForHStrainDomFlag ≡ true

    boundaryHBCorrectCloseabilityRecorded :
      Bool

    boundaryHBCorrectCloseabilityRecordedIsTrue :
      boundaryHBCorrectCloseabilityRecorded ≡ true

    boundaryHBPromoted :
      Bool

    boundaryHBPromotedIsFalse :
      boundaryHBPromoted ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    boundaryHBAssemblyStatement :
      String

    boundaryHBAssemblyStatementIsCanonical :
      boundaryHBAssemblyStatement ≡ boundaryHBAssemblyStatementText

    promotionFlags :
      List BoundaryHBAssemblyPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    pointwiseRouteProjection :
      List BoundaryHBPointwiseRouteProjection

    pointwiseRouteProjectionIsCanonical :
      pointwiseRouteProjection ≡ canonicalBoundaryHBPointwiseRouteProjection

    pointwiseRouteProjectionStatement :
      String

    pointwiseRouteProjectionStatementIsCanonical :
      pointwiseRouteProjectionStatement
      ≡ boundaryHBPointwiseRouteProjectionStatement

    pointwiseRouteReceipt :
      BoundaryHBPointwiseRouteReceipt

    pointwiseRouteReceiptIsCanonical :
      pointwiseRouteReceipt ≡ canonicalBoundaryHBPointwiseRouteReceipt

    receiptBoundary :
      List String

open Lambda2PlusTransportInequalityReceipt public
open BoundaryHBAssemblyReceipt public

canonicalLambda2PlusTransportInequalityReceipt :
  Lambda2PlusTransportInequalityReceipt
canonicalLambda2PlusTransportInequalityReceipt =
  record
    { status =
        lambda2PlusTransportShapeRecordedStandardWriteNow
    ; statusIsCanonical =
        refl
    ; tokens =
        canonicalLambda2PlusTransportInequalityTokens
    ; tokensAreCanonical =
        refl
    ; transportInequalityStatement =
        lambda2PlusTransportInequalityStatement
    ; transportInequalityStatementIsCanonical =
        refl
    ; standardWriteNow =
        true
    ; standardWriteNowIsTrue =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "lambda2plus_transport_ineq is standard/write-now"
        ∷ "No transport theorem is promoted here"
        ∷ "Clay promotion remains false"
        ∷ []
    }

canonicalBoundaryHBAssemblyReceipt :
  BoundaryHBAssemblyReceipt
canonicalBoundaryHBAssemblyReceipt =
  record
    { status =
        boundaryHBCorrectPointwiseRouteRecordedCandidateOnly
    ; statusIsCanonical =
        refl
    ; blockers =
        canonicalBoundaryHBAssemblyBlockers
    ; blockersAreCanonical =
        refl
    ; pointwiseKornBiaxialBoundRequired =
        true
    ; pointwiseKornBiaxialBoundRequiredIsTrue =
        refl
    ; lambda2ZeroRequired =
        true
    ; lambda2ZeroRequiredIsTrue =
        refl
    ; lambda1EqualsNegativeLambda3Required =
        true
    ; lambda1EqualsNegativeLambda3RequiredIsTrue =
        refl
    ; lambda3AtLeastLambdaMinRequired =
        true
    ; lambda3AtLeastLambdaMinRequiredIsTrue =
        refl
    ; biaxialBoundaryRequired =
        true
    ; biaxialBoundaryRequiredIsTrue =
        refl
    ; lambda3GapRequired =
        true
    ; lambda3GapRequiredIsTrue =
        refl
    ; pointwiseNabla2ULowerBoundEtaRequired =
        true
    ; pointwiseNabla2ULowerBoundEtaRequiredIsTrue =
        refl
    ; pointwiseMaxBKAtLeastB0Required =
        true
    ; pointwiseMaxBKAtLeastB0RequiredIsTrue =
        refl
    ; integralKornPlusContinuityInsufficientFlag =
        true
    ; integralKornPlusContinuityInsufficientFlagIsTrue =
        refl
    ; kornLevelSetOpenForHStrainDomFlag =
        true
    ; kornLevelSetOpenForHStrainDomFlagIsTrue =
        refl
    ; boundaryHBCorrectCloseabilityRecorded =
        true
    ; boundaryHBCorrectCloseabilityRecordedIsTrue =
        refl
    ; boundaryHBPromoted =
        false
    ; boundaryHBPromotedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; boundaryHBAssemblyStatement =
        boundaryHBAssemblyStatementText
    ; boundaryHBAssemblyStatementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; pointwiseRouteProjection =
        canonicalBoundaryHBPointwiseRouteProjection
    ; pointwiseRouteProjectionIsCanonical =
        refl
    ; pointwiseRouteProjectionStatement =
        boundaryHBPointwiseRouteProjectionStatement
    ; pointwiseRouteProjectionStatementIsCanonical =
        refl
    ; pointwiseRouteReceipt =
        canonicalBoundaryHBPointwiseRouteReceipt
    ; pointwiseRouteReceiptIsCanonical =
        refl
    ; receiptBoundary =
        "lambda2plus_transport_ineq is standard/write-now"
        ∷ "BoundaryHB_Correct closes only through the pointwise route lambda2 = 0, lambda1 = -lambda3, lambda3 >= lambda_min, and ||nabla^2 u|| >= eta"
        ∷ "The pointwise consequence max_k B_k >= b0 is recorded"
        ∷ "Integral Korn plus continuity is not the closure route"
        ∷ "KornLevelSet remains open for h_strain_dom"
        ∷ "Clay promotion stays false"
        ∷ []
    }

boundaryHBPointwiseRouteReceiptProjectionIsCanonical :
  routeProjection canonicalBoundaryHBPointwiseRouteReceipt
  ≡ canonicalBoundaryHBPointwiseRouteProjection
boundaryHBPointwiseRouteReceiptProjectionIsCanonical =
  refl

boundaryHBPointwiseRouteReceiptStatementIsCanonical :
  routeStatement canonicalBoundaryHBPointwiseRouteReceipt
  ≡ boundaryHBPointwiseRouteStatement
boundaryHBPointwiseRouteReceiptStatementIsCanonical =
  refl

boundaryHBPointwiseRouteReceiptKatoFormulaStatementIsCanonical :
  katoSecondDerivativeFormulaStatement canonicalBoundaryHBPointwiseRouteReceipt
  ≡ boundaryHBPointwiseKatoFormulaStatement
boundaryHBPointwiseRouteReceiptKatoFormulaStatementIsCanonical =
  refl

boundaryHBPointwiseRouteReceiptB0StatementIsCanonical :
  b0RecordedStatement canonicalBoundaryHBPointwiseRouteReceipt
  ≡ boundaryHBPointwiseB0Statement
boundaryHBPointwiseRouteReceiptB0StatementIsCanonical =
  refl

boundaryHBPointwiseRouteReceiptIntegralKornInsufficient :
  integralKornPlusContinuityInsufficientRouteFlag
    canonicalBoundaryHBPointwiseRouteReceipt
  ≡ true
boundaryHBPointwiseRouteReceiptIntegralKornInsufficient =
  refl

boundaryHBPointwiseRouteReceiptKornLevelSetOpen :
  kornLevelSetRemainsOpen canonicalBoundaryHBPointwiseRouteReceipt ≡ true
boundaryHBPointwiseRouteReceiptKornLevelSetOpen =
  refl

boundaryHBPointwiseRouteReceiptKeepsClayFalse :
  clayPromotion canonicalBoundaryHBPointwiseRouteReceipt ≡ false
boundaryHBPointwiseRouteReceiptKeepsClayFalse =
  refl

boundaryHBAssemblyKeepsIntegralKornInsufficient :
  integralKornPlusContinuityInsufficientFlag canonicalBoundaryHBAssemblyReceipt ≡ true
boundaryHBAssemblyKeepsIntegralKornInsufficient =
  refl

boundaryHBAssemblyKeepsKornLevelSetOpen :
  kornLevelSetOpenForHStrainDomFlag canonicalBoundaryHBAssemblyReceipt ≡ true
boundaryHBAssemblyKeepsKornLevelSetOpen =
  refl

boundaryHBAssemblyKeepsClayFalse :
  boundaryHBPromoted canonicalBoundaryHBAssemblyReceipt ≡ false
boundaryHBAssemblyKeepsClayFalse =
  refl
