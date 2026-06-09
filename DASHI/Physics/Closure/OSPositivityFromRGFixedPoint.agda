module DASHI.Physics.Closure.OSPositivityFromRGFixedPoint where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierFactorVecInjectivityOSPositivity as FiniteOS
import DASHI.Physics.Closure.RGBanachFixedPointReceipt as Banach

------------------------------------------------------------------------
-- OS positivity preservation from a future RG fixed point.
--
-- If the base Hamiltonian H0 is OS-positive and the RG flow is monotone in
-- the OS-positive cone, then the fixed point H* would inherit OS positivity.
-- The base check and RG fixed point proof are blockers; Wightman and Clay
-- promotions remain false.

data OSPositivityPreservationInput : Set where
  finiteCarrierOSPositivity :
    OSPositivityPreservationInput

  rgMonotoneOSPositiveConeMap :
    OSPositivityPreservationInput

  rgFixedPointHStar :
    OSPositivityPreservationInput

canonicalOSPositivityPreservationInputs :
  List OSPositivityPreservationInput
canonicalOSPositivityPreservationInputs =
  finiteCarrierOSPositivity
  ∷ rgMonotoneOSPositiveConeMap
  ∷ rgFixedPointHStar
  ∷ []

data OSPositivityFromRGBlocker : Set where
  missingH0OSPositivityCheckForRGHamiltonian :
    OSPositivityFromRGBlocker

  missingRGFixedPointConstruction :
    OSPositivityFromRGBlocker

  missingOSPositiveConeMonotonicityProof :
    OSPositivityFromRGBlocker

  missingOSWightmanReconstructionApplication :
    OSPositivityFromRGBlocker

canonicalOSPositivityFromRGBlockers :
  List OSPositivityFromRGBlocker
canonicalOSPositivityFromRGBlockers =
  missingH0OSPositivityCheckForRGHamiltonian
  ∷ missingRGFixedPointConstruction
  ∷ missingOSPositiveConeMonotonicityProof
  ∷ missingOSWightmanReconstructionApplication
  ∷ []

record OSPositivityFromRGFixedPointReceipt : Setω where
  field
    finiteOSReceipt :
      FiniteOS.CarrierFactorVecInjectivityOSPositivityReceipt

    finiteOSPositivityRecorded :
      FiniteOS.osPositivityInhabited finiteOSReceipt ≡ true

    banachReceipt :
      Banach.RGBanachFixedPointReceipt

    rgFixedPointStillOpen :
      Banach.uniqueFixedPointConstructed banachReceipt ≡ false

    inputs :
      List OSPositivityPreservationInput

    inputsAreCanonical :
      inputs ≡ canonicalOSPositivityPreservationInputs

    h0OSPositivityCheckForRGHamiltonian :
      Bool

    h0OSPositivityCheckForRGHamiltonianIsFalse :
      h0OSPositivityCheckForRGHamiltonian ≡ false

    osPositiveConeMonotonicityProved :
      Bool

    osPositiveConeMonotonicityProvedIsFalse :
      osPositiveConeMonotonicityProved ≡ false

    hStarOSPositivityConstructed :
      Bool

    hStarOSPositivityConstructedIsFalse :
      hStarOSPositivityConstructed ≡ false

    wightmanReconstructionApplied :
      Bool

    wightmanReconstructionAppliedIsFalse :
      wightmanReconstructionApplied ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    blockers :
      List OSPositivityFromRGBlocker

    blockersAreCanonical :
      blockers ≡ canonicalOSPositivityFromRGBlockers

    receiptBoundary :
      List String

open OSPositivityFromRGFixedPointReceipt public

canonicalOSPositivityFromRGFixedPointReceipt :
  OSPositivityFromRGFixedPointReceipt
canonicalOSPositivityFromRGFixedPointReceipt =
  record
    { finiteOSReceipt =
        FiniteOS.canonicalCarrierFactorVecInjectivityOSPositivityReceipt
    ; finiteOSPositivityRecorded =
        refl
    ; banachReceipt =
        Banach.canonicalRGBanachFixedPointReceipt
    ; rgFixedPointStillOpen =
        refl
    ; inputs =
        canonicalOSPositivityPreservationInputs
    ; inputsAreCanonical =
        refl
    ; h0OSPositivityCheckForRGHamiltonian =
        false
    ; h0OSPositivityCheckForRGHamiltonianIsFalse =
        refl
    ; osPositiveConeMonotonicityProved =
        false
    ; osPositiveConeMonotonicityProvedIsFalse =
        refl
    ; hStarOSPositivityConstructed =
        false
    ; hStarOSPositivityConstructedIsFalse =
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
        canonicalOSPositivityFromRGBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "Finite carrier OS positivity is consumed from FactorVec injectivity"
        ∷ "The RG-Hamiltonian H0 OS check, RG fixed point, and OS-positive cone monotonicity proofs are still missing"
        ∷ "Wightman reconstruction and Clay Yang-Mills promotion remain false"
        ∷ []
    }

osPositivityFromRGConsumesFiniteOS :
  FiniteOS.osPositivityInhabited
    (finiteOSReceipt canonicalOSPositivityFromRGFixedPointReceipt)
  ≡
  true
osPositivityFromRGConsumesFiniteOS =
  refl

osPositivityFromRGFixedPointStillOpen :
  hStarOSPositivityConstructed
    canonicalOSPositivityFromRGFixedPointReceipt
  ≡
  false
osPositivityFromRGFixedPointStillOpen =
  refl

osPositivityFromRGDoesNotPromoteClay :
  clayYangMillsPromoted canonicalOSPositivityFromRGFixedPointReceipt
  ≡
  false
osPositivityFromRGDoesNotPromoteClay =
  refl
