module DASHI.Physics.Closure.NSTriadKNHardProjectorParsevalTransportExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011. DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Transport finite coefficient-space self-adjointness across an explicitly
-- supplied Hermitian Parseval identification.  The coefficient-unitary model
-- is inhabited by taking the selected pairing to be the finite Fourier
-- pairing itself.  Identifying that selected pairing with the repository's
-- official physical L2 carrier remains a separate finite-sum/norm leaf and is
-- therefore not marked closed in this module.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNHardProjectorCoefficientSelfAdjointExact as Coefficient

record PeriodicHermitianParsevalTransport
    {r : Level}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (modes : List Z3.FourierMode) : Set (lsuc r) where
  field
    selectedHermitianPairing :
      LP.FourierField model →
      LP.FourierField model →
      C3.Complex (LP.realField model)

    pairingParseval :
      (left right : LP.FourierField model) →
      Coefficient.coefficientHermitianPairing model modes left right
        ≡ selectedHermitianPairing left right

open PeriodicHermitianParsevalTransport public

coefficientUnitaryHermitianParseval :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (modes : List Z3.FourierMode) →
  PeriodicHermitianParsevalTransport model modes
coefficientUnitaryHermitianParseval model modes = record
  { selectedHermitianPairing =
      Coefficient.coefficientHermitianPairing model modes
  ; pairingParseval = λ left right → refl
  }

hardLowSelectedPairingSelfAdjoint :
  ∀ {r}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode} →
  (P : PeriodicHermitianParsevalTransport model modes) →
  (cutoff : Nat) →
  (left right : LP.FourierField model) →
  selectedHermitianPairing P
    (Coefficient.hardLowCoefficientField model cutoff left) right
    ≡
  selectedHermitianPairing P
    left (Coefficient.hardLowCoefficientField model cutoff right)
hardLowSelectedPairingSelfAdjoint {model = model} {modes = modes}
  P cutoff left right =
  trans
    (sym (pairingParseval P
      (Coefficient.hardLowCoefficientField model cutoff left)
      right))
    (trans
      (Coefficient.hardLowCoefficientSelfAdjoint
        model modes cutoff left right)
      (pairingParseval P left
        (Coefficient.hardLowCoefficientField model cutoff right)))

hardHighSelectedPairingSelfAdjoint :
  ∀ {r}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode} →
  (P : PeriodicHermitianParsevalTransport model modes) →
  (cutoff : Nat) →
  (left right : LP.FourierField model) →
  selectedHermitianPairing P
    (Coefficient.hardHighCoefficientField model cutoff left) right
    ≡
  selectedHermitianPairing P
    left (Coefficient.hardHighCoefficientField model cutoff right)
hardHighSelectedPairingSelfAdjoint {model = model} {modes = modes}
  P cutoff left right =
  trans
    (sym (pairingParseval P
      (Coefficient.hardHighCoefficientField model cutoff left)
      right))
    (trans
      (Coefficient.hardHighCoefficientSelfAdjoint
        model modes cutoff left right)
      (pairingParseval P left
        (Coefficient.hardHighCoefficientField model cutoff right)))

record HardProjectorOrthogonalCertificate
    {r : Level}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (modes : List Z3.FourierMode)
    (cutoff : Nat) : Set (lsuc r) where
  field
    parseval : PeriodicHermitianParsevalTransport model modes

    lowSelfAdjoint :
      (left right : LP.FourierField model) →
      selectedHermitianPairing parseval
        (Coefficient.hardLowCoefficientField model cutoff left) right
        ≡
      selectedHermitianPairing parseval
        left (Coefficient.hardLowCoefficientField model cutoff right)

    highSelfAdjoint :
      (left right : LP.FourierField model) →
      selectedHermitianPairing parseval
        (Coefficient.hardHighCoefficientField model cutoff left) right
        ≡
      selectedHermitianPairing parseval
        left (Coefficient.hardHighCoefficientField model cutoff right)

    lowIdempotent :
      (field : LP.FourierField model) →
      (mode : Z3.FourierMode) →
      Coefficient.hardLowCoefficientField model cutoff
        (Coefficient.hardLowCoefficientField model cutoff field) mode
        ≡ Coefficient.hardLowCoefficientField model cutoff field mode

    highIdempotent :
      (field : LP.FourierField model) →
      (mode : Z3.FourierMode) →
      Coefficient.hardHighCoefficientField model cutoff
        (Coefficient.hardHighCoefficientField model cutoff field) mode
        ≡ Coefficient.hardHighCoefficientField model cutoff field mode

open HardProjectorOrthogonalCertificate public

coefficientUnitaryHardProjectorOrthogonal :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (modes : List Z3.FourierMode)
    (cutoff : Nat) →
  HardProjectorOrthogonalCertificate model modes cutoff
coefficientUnitaryHardProjectorOrthogonal model modes cutoff = record
  { parseval = coefficientUnitaryHermitianParseval model modes
  ; lowSelfAdjoint = hardLowSelectedPairingSelfAdjoint
      (coefficientUnitaryHermitianParseval model modes) cutoff
  ; highSelfAdjoint = hardHighSelectedPairingSelfAdjoint
      (coefficientUnitaryHermitianParseval model modes) cutoff
  ; lowIdempotent =
      Coefficient.hardLowCoefficientIdempotent model cutoff
  ; highIdempotent =
      Coefficient.hardHighCoefficientIdempotent model cutoff
  }

hardProjectorPairingParsevalTransportSurfaceConstructed : Bool
hardProjectorPairingParsevalTransportSurfaceConstructed = true

coefficientUnitaryHardProjectorOrthogonalConstructed : Bool
coefficientUnitaryHardProjectorOrthogonalConstructed = true

officialPhysicalHermitianParsevalTransportSelected : Bool
officialPhysicalHermitianParsevalTransportSelected = false

hardProjectorPairingParsevalTransportSurfaceConstructedIsTrue :
  hardProjectorPairingParsevalTransportSurfaceConstructed ≡ true
hardProjectorPairingParsevalTransportSurfaceConstructedIsTrue = refl

coefficientUnitaryHardProjectorOrthogonalConstructedIsTrue :
  coefficientUnitaryHardProjectorOrthogonalConstructed ≡ true
coefficientUnitaryHardProjectorOrthogonalConstructedIsTrue = refl

officialPhysicalHermitianParsevalTransportSelectedIsFalse :
  officialPhysicalHermitianParsevalTransportSelected ≡ false
officialPhysicalHermitianParsevalTransportSelectedIsFalse = refl

-- Compatibility aliases retained for the focused integration lane.  They refer
-- to the supplied/selected pairing, not an independently identified official
-- physical L2 pairing.
hardProjectorPairingParsevalTransportClosed : Bool
hardProjectorPairingParsevalTransportClosed =
  hardProjectorPairingParsevalTransportSurfaceConstructed

hardProjectorOrthogonalCertificateConstructed : Bool
hardProjectorOrthogonalCertificateConstructed =
  coefficientUnitaryHardProjectorOrthogonalConstructed

hardProjectorPairingParsevalTransportClosedIsTrue :
  hardProjectorPairingParsevalTransportClosed ≡ true
hardProjectorPairingParsevalTransportClosedIsTrue =
  hardProjectorPairingParsevalTransportSurfaceConstructedIsTrue

hardProjectorOrthogonalCertificateConstructedIsTrue :
  hardProjectorOrthogonalCertificateConstructed ≡ true
hardProjectorOrthogonalCertificateConstructedIsTrue =
  coefficientUnitaryHardProjectorOrthogonalConstructedIsTrue
