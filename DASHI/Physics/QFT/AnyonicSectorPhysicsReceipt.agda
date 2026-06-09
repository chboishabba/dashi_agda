module DASHI.Physics.QFT.AnyonicSectorPhysicsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.ConformalSpinFromCMReceipt as CMSpin
import DASHI.Physics.QFT.FiniteDHRAbelianReconstructionReceipt as FiniteDHR

------------------------------------------------------------------------
-- Anyonic-sector physics diagnostic receipt.
--
-- This module records the interpretation boundary for the prime-lane
-- sectors visible from the characteristic-zero CM character algebra.  The
-- current data is a 2+1D anyonic diagnostic surface.  It is not a direct
-- 3+1D fundamental quark/fermion field identification.  A 3+1D fermion
-- might be targeted through a paired anyon mechanism, but that mechanism is
-- open here and no full 3+1D fermion derivation is promoted.

data AnyonicSectorPhysicsStatus : Set where
  twoPlusOneDAnyonicDiagnosticOnly :
    AnyonicSectorPhysicsStatus

data AnyonicSectorPhysicsBlocker : Set where
  missingAnyonPairingMechanism :
    AnyonicSectorPhysicsBlocker

  missingThreePlusOneDSpinStatisticsLift :
    AnyonicSectorPhysicsBlocker

  missingDirectQuarkFieldConstruction :
    AnyonicSectorPhysicsBlocker

  missingFullFermionDerivation :
    AnyonicSectorPhysicsBlocker

canonicalAnyonicSectorPhysicsBlockers :
  List AnyonicSectorPhysicsBlocker
canonicalAnyonicSectorPhysicsBlockers =
  missingAnyonPairingMechanism
  ∷ missingThreePlusOneDSpinStatisticsLift
  ∷ missingDirectQuarkFieldConstruction
  ∷ missingFullFermionDerivation
  ∷ []

data AnyonicSectorPhysicsPromotionFlag : Set where

anyonicSectorPhysicsPromotionFlagImpossibleHere :
  AnyonicSectorPhysicsPromotionFlag →
  ⊥
anyonicSectorPhysicsPromotionFlagImpossibleHere ()

charZeroCMCharacterAlgebraLabel : String
charZeroCMCharacterAlgebraLabel =
  "characteristic-zero CM character algebra"

twoPlusOneDAnyonicDiagnosticLabel : String
twoPlusOneDAnyonicDiagnosticLabel =
  "prime-lane sectors from characteristic-zero CM character algebra are anyonic/2+1D diagnostic sectors"

notDirectThreePlusOneDFermionLabel : String
notDirectThreePlusOneDFermionLabel =
  "the diagnostic sectors are not direct 3+1D fundamental quark or fermion fields"

anyonPairCandidateLabel : String
anyonPairCandidateLabel =
  "a 3+1D fermion-from-anyon-pair route is a candidate only"

record AnyonicSectorPhysicsReceipt : Setω where
  field
    finiteDHRAbelianReceipt :
      FiniteDHR.FiniteDHRAbelianReconstructionReceipt

    conformalSpinFromCMReceipt :
      CMSpin.ConformalSpinFromCMReceipt

    status :
      AnyonicSectorPhysicsStatus

    statusIs2Plus1DAnyonicDiagnosticOnly :
      status ≡ twoPlusOneDAnyonicDiagnosticOnly

    sourceAlgebra :
      String

    sourceAlgebraIsCharZeroCMCharacterAlgebra :
      sourceAlgebra ≡ charZeroCMCharacterAlgebraLabel

    diagnosticStatement :
      String

    diagnosticStatementIsCanonical :
      diagnosticStatement ≡ twoPlusOneDAnyonicDiagnosticLabel

    notDirect3Plus1DFermionStatement :
      String

    notDirect3Plus1DFermionStatementIsCanonical :
      notDirect3Plus1DFermionStatement ≡ notDirectThreePlusOneDFermionLabel

    primeLaneSectorsAnyonicIn2Plus1 :
      Bool

    primeLaneSectorsAnyonicIn2Plus1IsTrue :
      primeLaneSectorsAnyonicIn2Plus1 ≡ true

    directQuarkFieldIdentification :
      Bool

    directQuarkFieldIdentificationIsFalse :
      directQuarkFieldIdentification ≡ false

    directThreePlusOneDFermionFieldIdentification :
      Bool

    directThreePlusOneDFermionFieldIdentificationIsFalse :
      directThreePlusOneDFermionFieldIdentification ≡ false

    fermionFromAnyonPairCandidate :
      Bool

    fermionFromAnyonPairCandidateIsTrue :
      fermionFromAnyonPairCandidate ≡ true

    fermionFromAnyonPairCandidateStatement :
      String

    fermionFromAnyonPairCandidateStatementIsCanonical :
      fermionFromAnyonPairCandidateStatement ≡ anyonPairCandidateLabel

    anyonPairingMechanismOpen :
      Bool

    anyonPairingMechanismOpenIsTrue :
      anyonPairingMechanismOpen ≡ true

    fullThreePlusOneDFermionDerivation :
      Bool

    fullThreePlusOneDFermionDerivationIsFalse :
      fullThreePlusOneDFermionDerivation ≡ false

    fullThreePlusOneDFermionPromotion :
      Bool

    fullThreePlusOneDFermionPromotionIsFalse :
      fullThreePlusOneDFermionPromotion ≡ false

    blockers :
      List AnyonicSectorPhysicsBlocker

    blockersAreCanonical :
      blockers ≡ canonicalAnyonicSectorPhysicsBlockers

    promotionFlags :
      List AnyonicSectorPhysicsPromotionFlag

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open AnyonicSectorPhysicsReceipt public

canonicalAnyonicSectorPhysicsReceipt :
  AnyonicSectorPhysicsReceipt
canonicalAnyonicSectorPhysicsReceipt =
  record
    { finiteDHRAbelianReceipt =
        FiniteDHR.canonicalFiniteDHRAbelianReconstructionReceipt
    ; conformalSpinFromCMReceipt =
        CMSpin.canonicalConformalSpinFromCMReceipt
    ; status =
        twoPlusOneDAnyonicDiagnosticOnly
    ; statusIs2Plus1DAnyonicDiagnosticOnly =
        refl
    ; sourceAlgebra =
        charZeroCMCharacterAlgebraLabel
    ; sourceAlgebraIsCharZeroCMCharacterAlgebra =
        refl
    ; diagnosticStatement =
        twoPlusOneDAnyonicDiagnosticLabel
    ; diagnosticStatementIsCanonical =
        refl
    ; notDirect3Plus1DFermionStatement =
        notDirectThreePlusOneDFermionLabel
    ; notDirect3Plus1DFermionStatementIsCanonical =
        refl
    ; primeLaneSectorsAnyonicIn2Plus1 =
        true
    ; primeLaneSectorsAnyonicIn2Plus1IsTrue =
        refl
    ; directQuarkFieldIdentification =
        false
    ; directQuarkFieldIdentificationIsFalse =
        refl
    ; directThreePlusOneDFermionFieldIdentification =
        false
    ; directThreePlusOneDFermionFieldIdentificationIsFalse =
        refl
    ; fermionFromAnyonPairCandidate =
        true
    ; fermionFromAnyonPairCandidateIsTrue =
        refl
    ; fermionFromAnyonPairCandidateStatement =
        anyonPairCandidateLabel
    ; fermionFromAnyonPairCandidateStatementIsCanonical =
        refl
    ; anyonPairingMechanismOpen =
        true
    ; anyonPairingMechanismOpenIsTrue =
        refl
    ; fullThreePlusOneDFermionDerivation =
        false
    ; fullThreePlusOneDFermionDerivationIsFalse =
        refl
    ; fullThreePlusOneDFermionPromotion =
        false
    ; fullThreePlusOneDFermionPromotionIsFalse =
        refl
    ; blockers =
        canonicalAnyonicSectorPhysicsBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Prime-lane sectors from the characteristic-zero CM character algebra are recorded as anyonic/2+1D diagnostic sectors"
        ∷ "They are not direct 3+1D fundamental quark fields or direct 3+1D fermion fields"
        ∷ "A fermion-from-anyon-pair route is retained only as a candidate"
        ∷ "The anyon-pairing mechanism remains open and the full 3+1D fermion derivation remains false"
        ∷ []
    }

primeLaneSectorsAreAnyonicIn2Plus1D :
  primeLaneSectorsAnyonicIn2Plus1 canonicalAnyonicSectorPhysicsReceipt
  ≡
  true
primeLaneSectorsAreAnyonicIn2Plus1D =
  refl

anyonicSectorReceiptRejectsDirectQuarkFieldIdentification :
  directQuarkFieldIdentification canonicalAnyonicSectorPhysicsReceipt
  ≡
  false
anyonicSectorReceiptRejectsDirectQuarkFieldIdentification =
  refl

anyonicSectorReceiptKeepsFermionFromAnyonPairCandidate :
  fermionFromAnyonPairCandidate canonicalAnyonicSectorPhysicsReceipt
  ≡
  true
anyonicSectorReceiptKeepsFermionFromAnyonPairCandidate =
  refl

anyonicSectorReceiptKeepsAnyonPairingMechanismOpen :
  anyonPairingMechanismOpen canonicalAnyonicSectorPhysicsReceipt
  ≡
  true
anyonicSectorReceiptKeepsAnyonPairingMechanismOpen =
  refl

anyonicSectorReceiptNoFullThreePlusOneDFermionDerivation :
  fullThreePlusOneDFermionDerivation canonicalAnyonicSectorPhysicsReceipt
  ≡
  false
anyonicSectorReceiptNoFullThreePlusOneDFermionDerivation =
  refl
