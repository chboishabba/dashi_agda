module DASHI.Physics.Closure.BinaryTetralemmaMarginStateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Algebra.TetralemmaBridge as Tet
import DASHI.Physics.Closure.Gate3NestingTaperConditionReceipt as Gate3
import DASHI.Physics.Closure.NSHminus1Over2ObstructionReceipt as NSHminus
import DASHI.Physics.Closure.NSTailRestrictedThetaDiagnosticReceipt as NSTail
import DASHI.Physics.Closure.ScaleGraphBarrierAlgebraProofReceipt as Algebra
import DASHI.Physics.Closure.YMKPThresholdCorrectionReceipt as YMKP

------------------------------------------------------------------------
-- Binary-to-tetralemma margin-state receipt.
--
-- The strict margin grammar is binary at the final barrier:
--
--   P + I < A
--   theta + epsilon < 1
--
-- so it can only conclude absorbed versus leaking.  The sprint diagnostics
-- show that this is too coarse for governance and analysis: convergence
-- without absorption, wrong-seam diagnostics, and mixed-domain readings must
-- be represented without promoting or discarding evidence.  This receipt maps
-- the binary barrier surface into a four-valued tetralemma state space.

data BinaryTetralemmaMarginStatus : Set where
  binaryTetralemmaMarginStateRecorded_noPromotion :
    BinaryTetralemmaMarginStatus

data MarginTetralemmaState : Set where
  marginTrueAbsorbed :
    MarginTetralemmaState

  marginFalseLeaking :
    MarginTetralemmaState

  marginBothMixed :
    MarginTetralemmaState

  marginNeitherWrongSeam :
    MarginTetralemmaState

canonicalMarginTetralemmaStates :
  List MarginTetralemmaState
canonicalMarginTetralemmaStates =
  marginTrueAbsorbed
  ∷ marginFalseLeaking
  ∷ marginBothMixed
  ∷ marginNeitherWrongSeam
  ∷ []

data MarginTetralemmaExample : Set where
  gate3DigitExpansionTrue :
    MarginTetralemmaExample

  nsHminusHalfUniformAbsorptionFalse :
    MarginTetralemmaExample

  ymConvergentButNotAbsorbingBoth :
    MarginTetralemmaExample

  nsGlobalThetaLowShellNeither :
    MarginTetralemmaExample

canonicalMarginTetralemmaExamples :
  List MarginTetralemmaExample
canonicalMarginTetralemmaExamples =
  gate3DigitExpansionTrue
  ∷ nsHminusHalfUniformAbsorptionFalse
  ∷ ymConvergentButNotAbsorbingBoth
  ∷ nsGlobalThetaLowShellNeither
  ∷ []

data MarginTetralemmaInterpretation : Set where
  trueMeansPressureDecreases :
    MarginTetralemmaInterpretation

  falseMeansAbsorberLoses :
    MarginTetralemmaInterpretation

  bothMeansConvergenceWithoutStrictAbsorptionOrMixedDiagnostics :
    MarginTetralemmaInterpretation

  neitherMeansOutOfDomainOrWrongSeam :
    MarginTetralemmaInterpretation

canonicalMarginTetralemmaInterpretations :
  List MarginTetralemmaInterpretation
canonicalMarginTetralemmaInterpretations =
  trueMeansPressureDecreases
  ∷ falseMeansAbsorberLoses
  ∷ bothMeansConvergenceWithoutStrictAbsorptionOrMixedDiagnostics
  ∷ neitherMeansOutOfDomainOrWrongSeam
  ∷ []

data BinaryTetralemmaMarginPromotion : Set where

binaryTetralemmaMarginPromotionImpossibleHere :
  BinaryTetralemmaMarginPromotion →
  ⊥
binaryTetralemmaMarginPromotionImpossibleHere ()

ymConvergenceBetaHundredths :
  Nat
ymConvergenceBetaHundredths =
  1011

ymAbsorptionBetaHundredths :
  Nat
ymAbsorptionBetaHundredths =
  1297

gate3SigmaDigitMillionths :
  Nat
gate3SigmaDigitMillionths =
  288675

gate3SigmaTaperP3Millionths :
  Nat
gate3SigmaTaperP3Millionths =
  318022

binaryBarrierStatement :
  String
binaryBarrierStatement =
  "The binary strict-margin barrier is P+I<A, equivalently theta+epsilon<1: it licenses absorbed versus leaking only."

tetralemmaStatement :
  String
tetralemmaStatement =
  "The diagnostics require four states: true=absorbed, false=leaking, both=mixed or convergent but not absorbing, neither=wrong seam or out of domain."

promotionBoundary :
  String
promotionBoundary =
  "This receipt refines margin governance only.  It does not prove PAWOTG, YM mass gap, NS regularity, Gate 3 closure, Clay, or terminal promotion."

record BinaryTetralemmaMarginStateReceipt : Setω where
  field
    status :
      BinaryTetralemmaMarginStatus

    statusIsCanonical :
      status ≡ binaryTetralemmaMarginStateRecorded_noPromotion

    algebraReceipt :
      Algebra.ScaleGraphBarrierAlgebraProofReceipt

    algebraRecorded :
      Algebra.algebraLemmaRecorded algebraReceipt ≡ true

    algebraKeepsClayFalse :
      Algebra.clayPromotion algebraReceipt ≡ false

    tetralemmaCarrier :
      Set

    tetralemmaCarrierIsExistingBridgeCarrier :
      tetralemmaCarrier ≡ Tet.TetralemmaPosition

    gate3Receipt :
      Gate3.Gate3NestingTaperConditionReceipt

    gate3DigitPassesTaper :
      Gate3.digitExpansionBelowStrictTaper gate3Receipt ≡ true

    gate3NoPromotion :
      Gate3.gate3Promoted gate3Receipt ≡ false

    nsObstructionReceipt :
      NSHminus.NSHminus1Over2ObstructionReceipt

    nsRatioDiverges :
      NSHminus.ratioDivergesAsNuToZero nsObstructionReceipt ≡ true

    nsNoClay :
      NSHminus.clayNavierStokesPromoted nsObstructionReceipt ≡ false

    nsTailReceipt :
      NSTail.NSTailRestrictedThetaDiagnosticReceipt

    nsGlobalThetaNotClaySeam :
      NSTail.thetaGlobalUsedForClaySeam nsTailReceipt ≡ false

    ymThresholdReceipt :
      YMKP.YMKPThresholdCorrectionReceipt

    ymPhysicalBetaDivergent :
      YMKP.physicalBetaKPDivergent ymThresholdReceipt ≡ true

    states :
      List MarginTetralemmaState

    statesAreCanonical :
      states ≡ canonicalMarginTetralemmaStates

    examples :
      List MarginTetralemmaExample

    examplesAreCanonical :
      examples ≡ canonicalMarginTetralemmaExamples

    interpretations :
      List MarginTetralemmaInterpretation

    interpretationsAreCanonical :
      interpretations ≡ canonicalMarginTetralemmaInterpretations

    ymConvergenceBeta :
      Nat

    ymConvergenceBetaIs1011 :
      ymConvergenceBeta ≡ ymConvergenceBetaHundredths

    ymAbsorptionBeta :
      Nat

    ymAbsorptionBetaIs1297 :
      ymAbsorptionBeta ≡ ymAbsorptionBetaHundredths

    gate3SigmaDigit :
      Nat

    gate3SigmaDigitIs0288675 :
      gate3SigmaDigit ≡ gate3SigmaDigitMillionths

    gate3SigmaTaperP3 :
      Nat

    gate3SigmaTaperP3Is0318022 :
      gate3SigmaTaperP3 ≡ gate3SigmaTaperP3Millionths

    fourValuedMarginGovernanceRecorded :
      Bool

    fourValuedMarginGovernanceRecordedIsTrue :
      fourValuedMarginGovernanceRecorded ≡ true

    binaryStateStillControlsPromotion :
      Bool

    binaryStateStillControlsPromotionIsTrue :
      binaryStateStillControlsPromotion ≡ true

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotions :
      List BinaryTetralemmaMarginPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      BinaryTetralemmaMarginPromotion →
      ⊥

    binaryText :
      String

    binaryTextIsCanonical :
      binaryText ≡ binaryBarrierStatement

    tetralemmaText :
      String

    tetralemmaTextIsCanonical :
      tetralemmaText ≡ tetralemmaStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ promotionBoundary

open BinaryTetralemmaMarginStateReceipt public

canonicalBinaryTetralemmaMarginStateReceipt :
  BinaryTetralemmaMarginStateReceipt
canonicalBinaryTetralemmaMarginStateReceipt =
  record
    { status =
        binaryTetralemmaMarginStateRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; algebraReceipt =
        Algebra.canonicalScaleGraphBarrierAlgebraProofReceipt
    ; algebraRecorded =
        refl
    ; algebraKeepsClayFalse =
        refl
    ; tetralemmaCarrier =
        Tet.TetralemmaPosition
    ; tetralemmaCarrierIsExistingBridgeCarrier =
        refl
    ; gate3Receipt =
        Gate3.canonicalGate3NestingTaperConditionReceipt
    ; gate3DigitPassesTaper =
        refl
    ; gate3NoPromotion =
        refl
    ; nsObstructionReceipt =
        NSHminus.canonicalNSHminus1Over2ObstructionReceipt
    ; nsRatioDiverges =
        refl
    ; nsNoClay =
        refl
    ; nsTailReceipt =
        NSTail.canonicalNSTailRestrictedThetaDiagnosticReceipt
    ; nsGlobalThetaNotClaySeam =
        refl
    ; ymThresholdReceipt =
        YMKP.canonicalYMKPThresholdCorrectionReceipt
    ; ymPhysicalBetaDivergent =
        refl
    ; states =
        canonicalMarginTetralemmaStates
    ; statesAreCanonical =
        refl
    ; examples =
        canonicalMarginTetralemmaExamples
    ; examplesAreCanonical =
        refl
    ; interpretations =
        canonicalMarginTetralemmaInterpretations
    ; interpretationsAreCanonical =
        refl
    ; ymConvergenceBeta =
        ymConvergenceBetaHundredths
    ; ymConvergenceBetaIs1011 =
        refl
    ; ymAbsorptionBeta =
        ymAbsorptionBetaHundredths
    ; ymAbsorptionBetaIs1297 =
        refl
    ; gate3SigmaDigit =
        gate3SigmaDigitMillionths
    ; gate3SigmaDigitIs0288675 =
        refl
    ; gate3SigmaTaperP3 =
        gate3SigmaTaperP3Millionths
    ; gate3SigmaTaperP3Is0318022 =
        refl
    ; fourValuedMarginGovernanceRecorded =
        true
    ; fourValuedMarginGovernanceRecordedIsTrue =
        refl
    ; binaryStateStillControlsPromotion =
        true
    ; binaryStateStillControlsPromotionIsTrue =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        binaryTetralemmaMarginPromotionImpossibleHere
    ; binaryText =
        binaryBarrierStatement
    ; binaryTextIsCanonical =
        refl
    ; tetralemmaText =
        tetralemmaStatement
    ; tetralemmaTextIsCanonical =
        refl
    ; boundary =
        promotionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalBinaryTetralemmaMarginNoClay :
  clayPromoted canonicalBinaryTetralemmaMarginStateReceipt ≡ false
canonicalBinaryTetralemmaMarginNoClay =
  refl
