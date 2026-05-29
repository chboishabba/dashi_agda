module DASHI.Physics.Closure.RGContractionExplicitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.RGContractionReceipt as RG

data RGDepthStepFormula : Set where
  weightedFactorVecParentSum : RGDepthStepFormula

data RGWeightedNormFormula : Set where
  alphaDepthWeightedCarrierNorm : RGWeightedNormFormula

data RGContractionExplicitBlocker : Set where
  missingParentFibreCardinalityBound : RGContractionExplicitBlocker
  missingWeightedNormProofInAgda : RGContractionExplicitBlocker
  missingEqualityWitnessOnDepthOneMode : RGContractionExplicitBlocker

canonicalRGContractionExplicitBlockers :
  List RGContractionExplicitBlocker
canonicalRGContractionExplicitBlockers =
  missingParentFibreCardinalityBound
  ∷ missingWeightedNormProofInAgda
  ∷ missingEqualityWitnessOnDepthOneMode
  ∷ []

rgExplicitOperatorStatement : String
rgExplicitOperatorStatement =
  "T_RG(v)_x = sum_{y -> x} alpha1 * v_y over FactorVec parent states y flowing to x"

rgExplicitNormStatement : String
rgExplicitNormStatement =
  "With ||v||_d = sum_x |v_x| alpha1^{-depth(x)}, the target estimate is ||T_RG v|| <= alpha1 ||v||, with equality on the depth-1 mode."

record RGContractionExplicitReceipt : Setω where
  field
    rgContractionReceipt :
      RG.RGContractionReceipt

    rgContractionStillOpen :
      RG.rgMapContractsProved rgContractionReceipt ≡ false

    operatorFormula :
      RGDepthStepFormula

    operatorFormulaRecorded :
      Bool

    operatorFormulaRecordedIsTrue :
      operatorFormulaRecorded ≡ true

    weightedNormFormula :
      RGWeightedNormFormula

    weightedNormFormulaRecorded :
      Bool

    weightedNormFormulaRecordedIsTrue :
      weightedNormFormulaRecorded ≡ true

    normInequalityTargetRecorded :
      Bool

    normInequalityTargetRecordedIsTrue :
      normInequalityTargetRecorded ≡ true

    operatorNormEqualityProvedHere :
      Bool

    operatorNormEqualityProvedHereIsFalse :
      operatorNormEqualityProvedHere ≡ false

    rgMapContractionProvedHere :
      Bool

    rgMapContractionProvedHereIsFalse :
      rgMapContractionProvedHere ≡ false

    banachFixedPointAppliedHere :
      Bool

    banachFixedPointAppliedHereIsFalse :
      banachFixedPointAppliedHere ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    explicitOperatorStatement :
      String

    explicitOperatorStatementIsCanonical :
      explicitOperatorStatement ≡ rgExplicitOperatorStatement

    explicitNormStatement :
      String

    explicitNormStatementIsCanonical :
      explicitNormStatement ≡ rgExplicitNormStatement

    blockers :
      List RGContractionExplicitBlocker

    blockersAreCanonical :
      blockers ≡ canonicalRGContractionExplicitBlockers

    receiptBoundary :
      List String

open RGContractionExplicitReceipt public

canonicalRGContractionExplicitReceipt :
  RGContractionExplicitReceipt
canonicalRGContractionExplicitReceipt =
  record
    { rgContractionReceipt =
        RG.canonicalRGContractionReceipt
    ; rgContractionStillOpen =
        refl
    ; operatorFormula =
        weightedFactorVecParentSum
    ; operatorFormulaRecorded =
        true
    ; operatorFormulaRecordedIsTrue =
        refl
    ; weightedNormFormula =
        alphaDepthWeightedCarrierNorm
    ; weightedNormFormulaRecorded =
        true
    ; weightedNormFormulaRecordedIsTrue =
        refl
    ; normInequalityTargetRecorded =
        true
    ; normInequalityTargetRecordedIsTrue =
        refl
    ; operatorNormEqualityProvedHere =
        false
    ; operatorNormEqualityProvedHereIsFalse =
        refl
    ; rgMapContractionProvedHere =
        false
    ; rgMapContractionProvedHereIsFalse =
        refl
    ; banachFixedPointAppliedHere =
        false
    ; banachFixedPointAppliedHereIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; explicitOperatorStatement =
        rgExplicitOperatorStatement
    ; explicitOperatorStatementIsCanonical =
        refl
    ; explicitNormStatement =
        rgExplicitNormStatement
    ; explicitNormStatementIsCanonical =
        refl
    ; blockers =
        canonicalRGContractionExplicitBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "The explicit FactorVec depth-step RG formula is now pinned down"
        ∷ "The weighted norm estimate is recorded as the next proof target"
        ∷ "The operator-norm equality, contraction proof, Banach application, and Clay promotion remain false"
        ∷ []
    }

rgContractionExplicitStillOpen :
  rgMapContractionProvedHere canonicalRGContractionExplicitReceipt ≡ false
rgContractionExplicitStillOpen =
  refl
