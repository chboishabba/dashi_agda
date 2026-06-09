module DASHI.Physics.Closure.OSAxiomsContinuumStatus where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierVEVReceipt as VEV
import DASHI.Physics.Closure.WightmanReconstructionCandidateReceipt as Wightman

data ContinuumOSAxiomBlocker : Set where
  os2FullO4CovarianceOpen : ContinuumOSAxiomBlocker
  os3BlockedOnPhysicalMassMatrixAndVEV : ContinuumOSAxiomBlocker
  osReconstructionStillExternal : ContinuumOSAxiomBlocker

canonicalContinuumOSAxiomBlockers : List ContinuumOSAxiomBlocker
canonicalContinuumOSAxiomBlockers =
  os2FullO4CovarianceOpen
  ∷ os3BlockedOnPhysicalMassMatrixAndVEV
  ∷ osReconstructionStillExternal
  ∷ []

osAxiomContinuumStatement : String
osAxiomContinuumStatement =
  "The OS axiom inventory is sharpened: OS3 is blocked on a VEV-calibrated physical mass matrix, while OS2 requires continuum O(4) restoration at the RG fixed point."

record OSAxiomsContinuumStatusReceipt : Setω where
  field
    wightmanCandidateReceipt :
      Wightman.WightmanReconstructionCandidateReceipt

    wightmanReconstructionStillOpen :
      Wightman.wightmanReconstructionApplied wightmanCandidateReceipt
      ≡
      false

    carrierVEVReceipt :
      VEV.CarrierVEVReceipt

    vevMassMatrixStillOpen :
      VEV.physicalMassMatrixFromVEV carrierVEVReceipt ≡ false

    os3BlockedOnVEV :
      Bool

    os3BlockedOnVEVIsTrue :
      os3BlockedOnVEV ≡ true

    os2FromRGFixedPoint :
      Bool

    os2FromRGFixedPointIsCandidate :
      os2FromRGFixedPoint ≡ true

    os2FormalReceiptConstructed :
      Bool

    os2FormalReceiptConstructedIsFalse :
      os2FormalReceiptConstructed ≡ false

    fullO4CovarianceProved :
      Bool

    fullO4CovarianceProvedIsFalse :
      fullO4CovarianceProved ≡ false

    reflectionPositivityProved :
      Bool

    reflectionPositivityProvedIsFalse :
      reflectionPositivityProved ≡ false

    wightmanReconstructionApplied :
      Bool

    wightmanReconstructionAppliedIsFalse :
      wightmanReconstructionApplied ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    blockers :
      List ContinuumOSAxiomBlocker

    blockersAreCanonical :
      blockers ≡ canonicalContinuumOSAxiomBlockers

    statement :
      String

    statementIsCanonical :
      statement ≡ osAxiomContinuumStatement

    receiptBoundary :
      List String

open OSAxiomsContinuumStatusReceipt public

canonicalOSAxiomsContinuumStatusReceipt :
  OSAxiomsContinuumStatusReceipt
canonicalOSAxiomsContinuumStatusReceipt =
  record
    { wightmanCandidateReceipt =
        Wightman.canonicalWightmanReconstructionCandidateReceipt
    ; wightmanReconstructionStillOpen =
        refl
    ; carrierVEVReceipt =
        VEV.canonicalCarrierVEVReceipt
    ; vevMassMatrixStillOpen =
        refl
    ; os3BlockedOnVEV =
        true
    ; os3BlockedOnVEVIsTrue =
        refl
    ; os2FromRGFixedPoint =
        true
    ; os2FromRGFixedPointIsCandidate =
        refl
    ; os2FormalReceiptConstructed =
        false
    ; os2FormalReceiptConstructedIsFalse =
        refl
    ; fullO4CovarianceProved =
        false
    ; fullO4CovarianceProvedIsFalse =
        refl
    ; reflectionPositivityProved =
        false
    ; reflectionPositivityProvedIsFalse =
        refl
    ; wightmanReconstructionApplied =
        false
    ; wightmanReconstructionAppliedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; blockers =
        canonicalContinuumOSAxiomBlockers
    ; blockersAreCanonical =
        refl
    ; statement =
        osAxiomContinuumStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "OS2 full Euclidean covariance is only a candidate from an eventual RG fixed point"
        ∷ "OS3 reflection positivity is blocked on the VEV-calibrated physical mass matrix"
        ∷ "Wightman reconstruction and Clay Yang-Mills promotion remain false"
        ∷ []
    }

osAxiomsContinuumStatusDoesNotPromoteClay :
  clayYangMillsPromoted canonicalOSAxiomsContinuumStatusReceipt ≡ false
osAxiomsContinuumStatusDoesNotPromoteClay =
  refl

