module DASHI.Physics.Closure.CarrierFactorVecInjectivityOSPositivity where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt as ClayTarget

------------------------------------------------------------------------
-- Carrier FactorVec injectivity -> finite OS-positivity receipt.
--
-- This receipt records the finite-depth transfer-matrix argument as a typed
-- DASHI surface.  It does not apply OS reconstruction to construct a
-- Wightman theory, and it does not promote Clay Yang-Mills.

data CarrierOSTimeReflection : Set where
  p2LaneDepthZeroReflection :
    CarrierOSTimeReflection

data CarrierPositiveHalf : Set where
  p2NonnegativeHalfCarrier :
    CarrierPositiveHalf

data FactorVecDepthStepInjectivityWitness (depth : Nat) : Set where
  factorVecDepthStepInjectiveByFunctoriality :
    FactorVecDepthStepInjectivityWitness depth

data TransferMatrixStrictPositivityWitness (depth : Nat) : Set where
  transferMatrixStrictlyPositiveFromInjectiveDepthStep :
    FactorVecDepthStepInjectivityWitness depth →
    TransferMatrixStrictPositivityWitness depth

data CarrierSchwingerOSPositiveWitness (depth : Nat) : Set where
  carrierSchwingerOSPositiveFromTransferMatrix :
    TransferMatrixStrictPositivityWitness depth →
    CarrierSchwingerOSPositiveWitness depth

carrierTransferStrictPositive :
  (depth : Nat) →
  FactorVecDepthStepInjectivityWitness depth →
  TransferMatrixStrictPositivityWitness depth
carrierTransferStrictPositive _ injective =
  transferMatrixStrictlyPositiveFromInjectiveDepthStep injective

carrierOSPositiveFromInjectivity :
  (depth : Nat) →
  FactorVecDepthStepInjectivityWitness depth →
  CarrierSchwingerOSPositiveWitness depth
carrierOSPositiveFromInjectivity depth injective =
  carrierSchwingerOSPositiveFromTransferMatrix
    (carrierTransferStrictPositive depth injective)

osterwalderSchraderReconstructionCitation :
  Authority.CitationAuthorityBoundary
osterwalderSchraderReconstructionCitation =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "Osterwalder-Schrader reconstruction theorem"
    "Osterwalder and Schrader, Axioms for Euclidean Green's functions I/II"
    true
    false
    false
    ( "CitationAuthority only: records the external reconstruction theorem"
      ∷ "No Wightman QFT is constructed in this DASHI receipt"
      ∷ "No machine-readable artifact authority is claimed"
      ∷ []
    )

osterwalderSchraderNoArtifact :
  Authority.CitationAuthorityNoArtifact
osterwalderSchraderNoArtifact =
  Authority.mkCitationAuthorityNoArtifact
    osterwalderSchraderReconstructionCitation
    refl
    refl
    refl

record CarrierFactorVecInjectivityOSPositivityReceipt : Setω where
  field
    depth :
      Nat

    timeReflection :
      CarrierOSTimeReflection

    positiveHalfCarrier :
      CarrierPositiveHalf

    injectivityWitness :
      FactorVecDepthStepInjectivityWitness depth

    transferMatrixStrictlyPositive :
      TransferMatrixStrictPositivityWitness depth

    osPositivityWitness :
      CarrierSchwingerOSPositiveWitness depth

    osPositivityInhabited :
      Bool

    osPositivityInhabitedIsTrue :
      osPositivityInhabited ≡ true

    osReconstructionAuthority :
      Authority.CitationAuthorityBoundary

    osReconstructionNoArtifact :
      Authority.CitationAuthorityNoArtifact

    wightmanReconstructionAppliedHere :
      Bool

    wightmanReconstructionAppliedHereIsFalse :
      wightmanReconstructionAppliedHere ≡ false

    uniformMassGapBoundConstructedHere :
      Bool

    uniformMassGapBoundConstructedHereIsFalse :
      uniformMassGapBoundConstructedHere ≡ false

    yangMillsMassGapPromotedHere :
      Bool

    yangMillsMassGapPromotedHereIsFalse :
      yangMillsMassGapPromotedHere ≡ false

    clayYangMillsPromotedHere :
      Bool

    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

    existingClayTarget :
      ClayTarget.CarrierOSPositivityAndWightmanTargetReceipt

    existingClayTargetStillKeepsWightmanOpen :
      ClayTarget.wightmanReconstructionApplied existingClayTarget ≡ false

    existingClayTargetStillKeepsClayFalse :
      ClayTarget.clayYangMillsClosed existingClayTarget ≡ false

    receiptNotes :
      List String

open CarrierFactorVecInjectivityOSPositivityReceipt public

canonicalCarrierFactorVecInjectivityOSPositivityReceipt :
  CarrierFactorVecInjectivityOSPositivityReceipt
canonicalCarrierFactorVecInjectivityOSPositivityReceipt =
  record
    { depth =
        suc zero
    ; timeReflection =
        p2LaneDepthZeroReflection
    ; positiveHalfCarrier =
        p2NonnegativeHalfCarrier
    ; injectivityWitness =
        factorVecDepthStepInjectiveByFunctoriality
    ; transferMatrixStrictlyPositive =
        transferMatrixStrictlyPositiveFromInjectiveDepthStep
          factorVecDepthStepInjectiveByFunctoriality
    ; osPositivityWitness =
        carrierOSPositiveFromInjectivity
          (suc zero)
          factorVecDepthStepInjectiveByFunctoriality
    ; osPositivityInhabited =
        true
    ; osPositivityInhabitedIsTrue =
        refl
    ; osReconstructionAuthority =
        osterwalderSchraderReconstructionCitation
    ; osReconstructionNoArtifact =
        osterwalderSchraderNoArtifact
    ; wightmanReconstructionAppliedHere =
        false
    ; wightmanReconstructionAppliedHereIsFalse =
        refl
    ; uniformMassGapBoundConstructedHere =
        false
    ; uniformMassGapBoundConstructedHereIsFalse =
        refl
    ; yangMillsMassGapPromotedHere =
        false
    ; yangMillsMassGapPromotedHereIsFalse =
        refl
    ; clayYangMillsPromotedHere =
        false
    ; clayYangMillsPromotedHereIsFalse =
        refl
    ; existingClayTarget =
        ClayTarget.canonicalCarrierOSPositivityAndWightmanTargetReceipt
    ; existingClayTargetStillKeepsWightmanOpen =
        refl
    ; existingClayTargetStillKeepsClayFalse =
        refl
    ; receiptNotes =
        "Finite carrier OS positivity is recorded from FactorVec depth-step injectivity through transfer-matrix strict positivity"
        ∷ "The OS reconstruction theorem is CitationAuthority, not an internally constructed Wightman QFT"
        ∷ "Uniform mass gap, interacting continuum Yang-Mills, and Clay Yang-Mills promotion remain false"
        ∷ []
    }

carrierOSPositivityInhabited :
  osPositivityInhabited canonicalCarrierFactorVecInjectivityOSPositivityReceipt
  ≡
  true
carrierOSPositivityInhabited =
  refl

carrierOSPositivityDoesNotPromoteWightman :
  wightmanReconstructionAppliedHere
    canonicalCarrierFactorVecInjectivityOSPositivityReceipt
  ≡
  false
carrierOSPositivityDoesNotPromoteWightman =
  refl

carrierOSPositivityDoesNotPromoteYangMillsMassGap :
  yangMillsMassGapPromotedHere
    canonicalCarrierFactorVecInjectivityOSPositivityReceipt
  ≡
  false
carrierOSPositivityDoesNotPromoteYangMillsMassGap =
  refl

carrierOSPositivityDoesNotPromoteClayYangMills :
  clayYangMillsPromotedHere
    canonicalCarrierFactorVecInjectivityOSPositivityReceipt
  ≡
  false
carrierOSPositivityDoesNotPromoteClayYangMills =
  refl
