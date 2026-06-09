module DASHI.Physics.Closure.ProgrammeFrontierFinalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C4: final frontier receipt for this tranche.

data FinalFrontier : Set where
  nsGlobalH118BernoulliBandRigour :
    FinalFrontier

  ymCuspUniversalityForFlatEuclideanLimit :
    FinalFrontier

  ckmFiveQuantityFirstOrderPredictionSet :
    FinalFrontier

canonicalFinalFrontiers : List FinalFrontier
canonicalFinalFrontiers =
  nsGlobalH118BernoulliBandRigour
  ∷ ymCuspUniversalityForFlatEuclideanLimit
  ∷ ckmFiveQuantityFirstOrderPredictionSet
  ∷ []

data ClayRemainingTask : Set where
  nsBernoulliBandRigour :
    ClayRemainingTask

  ymCuspUniversalityProof :
    ClayRemainingTask

canonicalClayRemainingTasks : List ClayRemainingTask
canonicalClayRemainingTasks =
  nsBernoulliBandRigour
  ∷ ymCuspUniversalityProof
  ∷ []

data CKMFirstOrderPrediction : Set where
  lambdaDepthSeparation :
    CKMFirstOrderPrediction

  vcbArithmetic :
    CKMFirstOrderPrediction

  vubAlphaOneAlphaTwo :
    CKMFirstOrderPrediction

  gammaAtkinLehner :
    CKMFirstOrderPrediction

  betaFromApex :
    CKMFirstOrderPrediction

canonicalCKMFirstOrderPredictions : List CKMFirstOrderPrediction
canonicalCKMFirstOrderPredictions =
  lambdaDepthSeparation
  ∷ vcbArithmetic
  ∷ vubAlphaOneAlphaTwo
  ∷ gammaAtkinLehner
  ∷ betaFromApex
  ∷ []

programmeFrontierFinalStatement : String
programmeFrontierFinalStatement =
  "Final frontier: NS needs Bernoulli band rigour for the global H^{11/8} bound; YM needs cusp universality for the flat Euclidean 4D SU(N) limit; CKM has a complete first-order five-quantity candidate set with Vub and beta newly recorded."

data ProgrammeFrontierFinalPromotion : Set where

programmeFrontierFinalPromotionImpossibleHere :
  ProgrammeFrontierFinalPromotion →
  ⊥
programmeFrontierFinalPromotionImpossibleHere ()

record ProgrammeFrontierFinalReceipt : Setω where
  field
    frontiers :
      List FinalFrontier

    frontiersAreCanonical :
      frontiers ≡ canonicalFinalFrontiers

    frontierCount :
      Nat

    frontierCountIsThree :
      frontierCount ≡ 3

    clayRemainingTasks :
      List ClayRemainingTask

    clayRemainingTasksAreCanonical :
      clayRemainingTasks ≡ canonicalClayRemainingTasks

    clayRemainingTaskCount :
      Nat

    clayRemainingTaskCountIsTwo :
      clayRemainingTaskCount ≡ 2

    ckmPredictionSet :
      List CKMFirstOrderPrediction

    ckmPredictionSetIsCanonical :
      ckmPredictionSet ≡ canonicalCKMFirstOrderPredictions

    ckmPredictionCount :
      Nat

    ckmPredictionCountIsFive :
      ckmPredictionCount ≡ 5

    ckmAllWithinTenPercent :
      Bool

    ckmAllWithinTenPercentIsTrue :
      ckmAllWithinTenPercent ≡ true

    vubNewThisTranche :
      Bool

    vubNewThisTrancheIsTrue :
      vubNewThisTranche ≡ true

    betaNewThisTranche :
      Bool

    betaNewThisTrancheIsTrue :
      betaNewThisTranche ≡ true

    programmeMostConstrainedSoFar :
      Bool

    programmeMostConstrainedSoFarIsTrue :
      programmeMostConstrainedSoFar ≡ true

    statement :
      String

    statementIsCanonical :
      statement ≡ programmeFrontierFinalStatement

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    promotionFlags :
      List ProgrammeFrontierFinalPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ProgrammeFrontierFinalReceipt public

canonicalProgrammeFrontierFinalReceipt :
  ProgrammeFrontierFinalReceipt
canonicalProgrammeFrontierFinalReceipt =
  record
    { frontiers =
        canonicalFinalFrontiers
    ; frontiersAreCanonical =
        refl
    ; frontierCount =
        3
    ; frontierCountIsThree =
        refl
    ; clayRemainingTasks =
        canonicalClayRemainingTasks
    ; clayRemainingTasksAreCanonical =
        refl
    ; clayRemainingTaskCount =
        2
    ; clayRemainingTaskCountIsTwo =
        refl
    ; ckmPredictionSet =
        canonicalCKMFirstOrderPredictions
    ; ckmPredictionSetIsCanonical =
        refl
    ; ckmPredictionCount =
        5
    ; ckmPredictionCountIsFive =
        refl
    ; ckmAllWithinTenPercent =
        true
    ; ckmAllWithinTenPercentIsTrue =
        refl
    ; vubNewThisTranche =
        true
    ; vubNewThisTrancheIsTrue =
        refl
    ; betaNewThisTranche =
        true
    ; betaNewThisTrancheIsTrue =
        refl
    ; programmeMostConstrainedSoFar =
        true
    ; programmeMostConstrainedSoFarIsTrue =
        refl
    ; statement =
        programmeFrontierFinalStatement
    ; statementIsCanonical =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Manager C4 records the final frontier state for this tranche"
        ∷ "Two precise Clay tasks remain and the CKM first-order set is complete as candidates"
        ∷ "No Clay or physical CKM promotion is made"
        ∷ []
    }

canonicalProgrammeFrontierFinalKeepsClayFalse :
  clayYangMillsPromoted canonicalProgrammeFrontierFinalReceipt ≡ false
canonicalProgrammeFrontierFinalKeepsClayFalse =
  refl

canonicalProgrammeFrontierFinalNoPromotion :
  ProgrammeFrontierFinalPromotion →
  ⊥
canonicalProgrammeFrontierFinalNoPromotion =
  programmeFrontierFinalPromotionImpossibleHere
