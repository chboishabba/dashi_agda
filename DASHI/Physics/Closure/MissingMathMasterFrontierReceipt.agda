module DASHI.Physics.Closure.MissingMathMasterFrontierReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Missing-math master frontier receipt.
--
-- Builtin-only ledger for the three unresolved mathematical walls.  The
-- gates below are identifiers only: this module records the current frontier
-- fail-closed and does not promote any Navier-Stokes, Yang-Mills, or
-- unification claim.

data MissingMathWall : Set where
  NSWall :
    MissingMathWall

  YMWall :
    MissingMathWall

  UnificationWall :
    MissingMathWall

canonicalWalls :
  List MissingMathWall
canonicalWalls =
  NSWall
  ∷ YMWall
  ∷ UnificationWall
  ∷ []

data NSGateCode : Set where
  AbelTriadicDefectMeasureConstruction :
    NSGateCode

  ApproximateTransferOperatorStationarity :
    NSGateCode

  LeiRenTianOutputSupportTransferToAbelMeasure :
    NSGateCode

  NSTypeIBlowupKappaBiasBound :
    NSGateCode

  PointwiseToAbelStretchingTransfer :
    NSGateCode

canonicalNSGateCodes :
  List NSGateCode
canonicalNSGateCodes =
  AbelTriadicDefectMeasureConstruction
  ∷ ApproximateTransferOperatorStationarity
  ∷ LeiRenTianOutputSupportTransferToAbelMeasure
  ∷ NSTypeIBlowupKappaBiasBound
  ∷ PointwiseToAbelStretchingTransfer
  ∷ []

data YMGateCode : Set where
  HamiltonianDominatesDefectPlusHolonomy :
    YMGateCode

  H3aTraceNormTransfer :
    YMGateCode

  H3bVacuumProjectionContinuity :
    YMGateCode

  NoSpectralPollutionBelowFiniteMargin :
    YMGateCode

  OSWightmanReconstructionCompatibility :
    YMGateCode

canonicalYMGateCodes :
  List YMGateCode
canonicalYMGateCodes =
  HamiltonianDominatesDefectPlusHolonomy
  ∷ H3aTraceNormTransfer
  ∷ H3bVacuumProjectionContinuity
  ∷ NoSpectralPollutionBelowFiniteMargin
  ∷ OSWightmanReconstructionCompatibility
  ∷ []

data UCTGateCode : Set where
  UCT1 :
    UCTGateCode

  UCT2 :
    UCTGateCode

  UCT3 :
    UCTGateCode

  UCT4 :
    UCTGateCode

  UCT5 :
    UCTGateCode

  UCT6 :
    UCTGateCode

  UCT7 :
    UCTGateCode

  UCT8 :
    UCTGateCode

canonicalUCTGateCodes :
  List UCTGateCode
canonicalUCTGateCodes =
  UCT1
  ∷ UCT2
  ∷ UCT3
  ∷ UCT4
  ∷ UCT5
  ∷ UCT6
  ∷ UCT7
  ∷ UCT8
  ∷ []

record FrontierWallReceipt : Set where
  field
    wall :
      MissingMathWall

    failClosed :
      Bool

    failClosedIsTrue :
      failClosed ≡ true

    promotionFlag :
      Bool

    promotionFlagIsFalse :
      promotionFlag ≡ false

open FrontierWallReceipt public

nsWallReceipt :
  FrontierWallReceipt
nsWallReceipt =
  record
    { wall =
        NSWall
    ; failClosed =
        true
    ; failClosedIsTrue =
        refl
    ; promotionFlag =
        false
    ; promotionFlagIsFalse =
        refl
    }

ymWallReceipt :
  FrontierWallReceipt
ymWallReceipt =
  record
    { wall =
        YMWall
    ; failClosed =
        true
    ; failClosedIsTrue =
        refl
    ; promotionFlag =
        false
    ; promotionFlagIsFalse =
        refl
    }

unificationWallReceipt :
  FrontierWallReceipt
unificationWallReceipt =
  record
    { wall =
        UnificationWall
    ; failClosed =
        true
    ; failClosedIsTrue =
        refl
    ; promotionFlag =
        false
    ; promotionFlagIsFalse =
        refl
    }

canonicalWallReceipts :
  List FrontierWallReceipt
canonicalWallReceipts =
  nsWallReceipt
  ∷ ymWallReceipt
  ∷ unificationWallReceipt
  ∷ []

record MissingMathMasterFrontierReceipt : Set where
  field
    walls :
      List MissingMathWall

    wallsAreCanonical :
      walls ≡ canonicalWalls

    nsGates :
      List NSGateCode

    nsGatesAreCanonical :
      nsGates ≡ canonicalNSGateCodes

    ymGates :
      List YMGateCode

    ymGatesAreCanonical :
      ymGates ≡ canonicalYMGateCodes

    uctGates :
      List UCTGateCode

    uctGatesAreCanonical :
      uctGates ≡ canonicalUCTGateCodes

    wallReceipts :
      List FrontierWallReceipt

    wallReceiptsAreCanonical :
      wallReceipts ≡ canonicalWallReceipts

    nsPromotionFlag :
      Bool

    nsPromotionFlagIsFalse :
      nsPromotionFlag ≡ false

    ymPromotionFlag :
      Bool

    ymPromotionFlagIsFalse :
      ymPromotionFlag ≡ false

    unificationPromotionFlag :
      Bool

    unificationPromotionFlagIsFalse :
      unificationPromotionFlag ≡ false

    summary :
      String

canonicalSummary :
  String
canonicalSummary =
  "Missing-math master frontier: NS, YM, and Unification remain fail-closed; NS has five named gates, YM has five named gates, UCT has eight gates, and all promotion flags are false."

canonicalMissingMathMasterFrontierReceipt :
  MissingMathMasterFrontierReceipt
canonicalMissingMathMasterFrontierReceipt =
  record
    { walls =
        canonicalWalls
    ; wallsAreCanonical =
        refl
    ; nsGates =
        canonicalNSGateCodes
    ; nsGatesAreCanonical =
        refl
    ; ymGates =
        canonicalYMGateCodes
    ; ymGatesAreCanonical =
        refl
    ; uctGates =
        canonicalUCTGateCodes
    ; uctGatesAreCanonical =
        refl
    ; wallReceipts =
        canonicalWallReceipts
    ; wallReceiptsAreCanonical =
        refl
    ; nsPromotionFlag =
        false
    ; nsPromotionFlagIsFalse =
        refl
    ; ymPromotionFlag =
        false
    ; ymPromotionFlagIsFalse =
        refl
    ; unificationPromotionFlag =
        false
    ; unificationPromotionFlagIsFalse =
        refl
    ; summary =
        canonicalSummary
    }

missingMathMasterFrontierSummary :
  String
missingMathMasterFrontierSummary =
  canonicalSummary
