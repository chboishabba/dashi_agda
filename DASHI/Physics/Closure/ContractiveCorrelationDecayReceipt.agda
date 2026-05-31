module DASHI.Physics.Closure.ContractiveCorrelationDecayReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.RGOperatorNormFormalProof as RG
import DASHI.Physics.Closure.UniformBoundStrongCouplingReceipt as Uniform

------------------------------------------------------------------------
-- Contractive correlation-decay bridge receipt.
--
-- This records the requested correlation-decay shape: a contractive depth/RG
-- mechanism gives a geometric-decay analogy, while finite strong-coupling
-- receipts already record exponential decay by an area law.  It does not
-- identify a continuum two-point function, derive a continuum mass gap, or
-- promote Clay Yang-Mills.

data ContractiveCorrelationDecayStatus : Set where
  contractiveDecayBridgeShapeRecordedOnly :
    ContractiveCorrelationDecayStatus

data ContractiveCorrelationDecayPiece : Set where
  normalizedRGContraction :
    ContractiveCorrelationDecayPiece

  strongCouplingExponentialDecay :
    ContractiveCorrelationDecayPiece

  geometricDepthDecayShape :
    ContractiveCorrelationDecayPiece

  continuumTwoPointMassGapOpen :
    ContractiveCorrelationDecayPiece

canonicalContractiveCorrelationDecayPieces :
  List ContractiveCorrelationDecayPiece
canonicalContractiveCorrelationDecayPieces =
  normalizedRGContraction
  ∷ strongCouplingExponentialDecay
  ∷ geometricDepthDecayShape
  ∷ continuumTwoPointMassGapOpen
  ∷ []

data ContractiveCorrelationDecayPromotion : Set where

contractiveCorrelationDecayPromotionImpossibleHere :
  ContractiveCorrelationDecayPromotion →
  ⊥
contractiveCorrelationDecayPromotionImpossibleHere ()

contractiveCorrelationDecayStatement : String
contractiveCorrelationDecayStatement =
  "Contractive carrier dynamics and finite strong-coupling exponential decay are recorded as a two-point decay bridge shape only; no continuum mass gap is derived."

record ContractiveCorrelationDecayReceipt : Setω where
  field
    status :
      ContractiveCorrelationDecayStatus

    statusIsCanonical :
      status ≡ contractiveDecayBridgeShapeRecordedOnly

    rgOperatorNormReceipt :
      RG.RGOperatorNormFormalProofReceipt

    normalizedRGContractionAvailable :
      RG.rgContractionForNormalizedMap rgOperatorNormReceipt ≡ true

    rgContinuumConvergenceStillOpen :
      RG.continuumRGConvergenceProved rgOperatorNormReceipt ≡ false

    uniformStrongCouplingReceipt :
      Uniform.UniformBoundStrongCouplingReceipt

    finiteExponentialDecayAvailable :
      Uniform.decayRateEqualsStringTension uniformStrongCouplingReceipt
      ≡ true

    continuumUniformBoundStillOpen :
      Uniform.continuumUniformBoundProved uniformStrongCouplingReceipt
      ≡ false

    geometricDecayShapeRecorded :
      Bool

    geometricDecayShapeRecordedIsTrue :
      geometricDecayShapeRecorded ≡ true

    continuumTwoPointFunctionConstructed :
      Bool

    continuumTwoPointFunctionConstructedIsFalse :
      continuumTwoPointFunctionConstructed ≡ false

    massGapFromContractionProved :
      Bool

    massGapFromContractionProvedIsFalse :
      massGapFromContractionProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    pieces :
      List ContractiveCorrelationDecayPiece

    piecesAreCanonical :
      pieces ≡ canonicalContractiveCorrelationDecayPieces

    promotionFlags :
      List ContractiveCorrelationDecayPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ contractiveCorrelationDecayStatement

    receiptBoundary :
      List String

open ContractiveCorrelationDecayReceipt public

canonicalContractiveCorrelationDecayReceipt :
  ContractiveCorrelationDecayReceipt
canonicalContractiveCorrelationDecayReceipt =
  record
    { status =
        contractiveDecayBridgeShapeRecordedOnly
    ; statusIsCanonical =
        refl
    ; rgOperatorNormReceipt =
        RG.canonicalRGOperatorNormFormalProofReceipt
    ; normalizedRGContractionAvailable =
        refl
    ; rgContinuumConvergenceStillOpen =
        refl
    ; uniformStrongCouplingReceipt =
        Uniform.canonicalUniformBoundStrongCouplingReceipt
    ; finiteExponentialDecayAvailable =
        refl
    ; continuumUniformBoundStillOpen =
        refl
    ; geometricDecayShapeRecorded =
        true
    ; geometricDecayShapeRecordedIsTrue =
        refl
    ; continuumTwoPointFunctionConstructed =
        false
    ; continuumTwoPointFunctionConstructedIsFalse =
        refl
    ; massGapFromContractionProved =
        false
    ; massGapFromContractionProvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; pieces =
        canonicalContractiveCorrelationDecayPieces
    ; piecesAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        contractiveCorrelationDecayStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Consumes RGOperatorNormFormalProof for normalized carrier contraction"
        ∷ "Consumes UniformBoundStrongCouplingReceipt for finite strong-coupling exponential decay"
        ∷ "Records only the bridge shape Delta = -log(lambda)/a"
        ∷ "Does not construct continuum two-point functions or derive a continuum mass gap"
        ∷ "Keeps all Clay Yang-Mills promotion flags false"
        ∷ []
    }

contractiveCorrelationDecayKeepsClayFalse :
  clayYangMillsPromoted canonicalContractiveCorrelationDecayReceipt ≡ false
contractiveCorrelationDecayKeepsClayFalse =
  refl
