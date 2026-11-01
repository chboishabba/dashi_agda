module DASHI.Analysis.SummableIncrementCauchyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- APPLICATION-NEUTRAL SUMMABLE-INCREMENT -> CAUCHY COMPILER
--
-- Cross-pollinated theorem shape from the Yang--Mills top-down RG lane:
-- convergence of one literal trajectory can be obtained from a summable bound
-- on its successive generated increments.  No global contraction theorem for
-- the whole state-transition map is required.
------------------------------------------------------------------------

generatedTail : (Nat → ℚ) → Nat → Nat → ℚ
generatedTail increment start zero = 0ℚ
generatedTail increment start (suc count) =
  increment start + generatedTail increment (suc start) count

record SummableIncrementProblem : Set₁ where
  field
    State : Set
    trajectory : Nat → State

    difference : Nat → Nat → ℚ
    differenceNonnegative : ∀ start count → 0ℚ ≤ difference start count

    generatedIncrement : Nat → ℚ
    generatedIncrementNonnegative : ∀ scale → 0ℚ ≤ generatedIncrement scale

    differenceBelowGeneratedTail : ∀ start count →
      difference start count
      ≤ generatedTail generatedIncrement start count

    cauchyTailBound : Nat → ℚ
    generatedTailBelowCauchyBound : ∀ start count →
      generatedTail generatedIncrement start count
      ≤ cauchyTailBound start

    tailBoundVanishes : Set
    reading : String

open SummableIncrementProblem public

cauchyDifferenceBound :
  (P : SummableIncrementProblem) →
  ∀ start count →
  difference P start count ≤ cauchyTailBound P start
cauchyDifferenceBound P start count =
  ℚP.≤-trans
    (differenceBelowGeneratedTail P start count)
    (generatedTailBelowCauchyBound P start count)

record ReverseConsumerObligations : Set₁ where
  field
    sameLiteralTrajectory : Set
    adjacentIncrementEstimate : Set
    telescopingOrTriangleTransport : Set
    summableTailMajorant : Set
    tailVanishesInConsumerMetric : Set
    reading : String

open ReverseConsumerObligations public

data SummableIncrementShapeAutomaticallyTransfersApplicationReceipt : Set where

data CauchyCompilerAutomaticallySuppliesIncrementEstimate : Set where

shapeDoesNotTransferPhysicalReceipt :
  SummableIncrementShapeAutomaticallyTransfersApplicationReceipt → ⊥
shapeDoesNotTransferPhysicalReceipt ()

compilerDoesNotInventTailEstimate :
  CauchyCompilerAutomaticallySuppliesIncrementEstimate → ⊥
compilerDoesNotInventTailEstimate ()

record BidiStatus : Set where
  field
    summableIncrementShapeOwned : Bool
    cauchyDifferenceCompilerOwned : Bool
    applicationIncrementEstimateReusable : Bool

    summableIncrementShapeOwnedIsTrue : summableIncrementShapeOwned ≡ true
    cauchyDifferenceCompilerOwnedIsTrue : cauchyDifferenceCompilerOwned ≡ true
    applicationIncrementEstimateReusableIsFalse : applicationIncrementEstimateReusable ≡ false

open BidiStatus public

canonicalBidiStatus : BidiStatus
canonicalBidiStatus = record
  { summableIncrementShapeOwned = true
  ; cauchyDifferenceCompilerOwned = true
  ; applicationIncrementEstimateReusable = false
  ; summableIncrementShapeOwnedIsTrue = refl
  ; cauchyDifferenceCompilerOwnedIsTrue = refl
  ; applicationIncrementEstimateReusableIsFalse = refl
  }
