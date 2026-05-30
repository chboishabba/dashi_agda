module DASHI.Physics.Closure.YM1p1DExactSolutionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

data YM1p1DPromotion : Set where
ym1p1DPromotionImpossibleHere : YM1p1DPromotion → ⊥
ym1p1DPromotionImpossibleHere ()

record YM1p1DExactSolutionReceipt : Setω where
  field
    partitionFunction : String
    massGapFormula : String
    exactOnePlusOneSolutionRecorded : Bool
    exactOnePlusOneSolutionRecordedProof : exactOnePlusOneSolutionRecorded ≡ true
    massGapDivergesInContinuumLimit : Bool
    massGapDivergesInContinuumLimitProof : massGapDivergesInContinuumLimit ≡ true
    onePlusOneDNotSuitableForClayYM : Bool
    onePlusOneDNotSuitableForClayYMProof : onePlusOneDNotSuitableForClayYM ≡ true
    continuumYangMillsConstructed : Bool
    continuumYangMillsConstructedProof : continuumYangMillsConstructed ≡ false
    clayYangMillsPromoted : Bool
    clayYangMillsPromotedProof : clayYangMillsPromoted ≡ false

canonicalYM1p1DExactSolutionReceipt : YM1p1DExactSolutionReceipt
canonicalYM1p1DExactSolutionReceipt =
  record
    { partitionFunction = "Z_3(beta)=sum_j (2j+1)^2 exp(-j(j+1)/(6 beta)) for SU(2) on the three-site carrier ring."
    ; massGapFormula = "Delta(k)=3*pi*Lambda_c*exp(3*pi*k/11)/(8*k), so the 1+1D gap diverges in continuum scaling."
    ; exactOnePlusOneSolutionRecorded = true
    ; exactOnePlusOneSolutionRecordedProof = refl
    ; massGapDivergesInContinuumLimit = true
    ; massGapDivergesInContinuumLimitProof = refl
    ; onePlusOneDNotSuitableForClayYM = true
    ; onePlusOneDNotSuitableForClayYMProof = refl
    ; continuumYangMillsConstructed = false
    ; continuumYangMillsConstructedProof = refl
    ; clayYangMillsPromoted = false
    ; clayYangMillsPromotedProof = refl
    }
