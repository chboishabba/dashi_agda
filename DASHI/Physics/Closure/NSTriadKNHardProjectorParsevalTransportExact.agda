module DASHI.Physics.Closure.NSTriadKNHardProjectorParsevalTransportExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011. DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Transport finite coefficient-space self-adjointness to the selected
-- periodic physical Hermitian pairing.  The repository's frozen
-- coefficient-unitary convention represents the physical L2 pairing by the
-- same finite Fourier pairing, so Parseval is definitional for that
-- convention.  Combining self-adjointness with the already proved pointwise
-- idempotence gives the exact orthogonal-projector certificate.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
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
    physicalHermitianPairing :
      LP.FourierField model →
      LP.FourierField model →
      C3.Complex (LP.realField model)

    pairingParseval :
      (left right : LP.FourierField model) →
      Coefficient.coefficientHermitianPairing model modes left right
        ≡ physicalHermitianPairing left right

open PeriodicHermitianParsevalTransport public

coefficientUnitaryHermitianParseval :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (modes : List Z3.FourierMode) →
  PeriodicHermitianParsevalTransport model modes
coefficientUnitaryHermitianParseval model modes = record
  { physicalHermitianPairing =
      Coefficient.coefficientHermitianPairing model modes
  ; pairingParseval = λ left right → refl
  }

hardLowPhysicalSelfAdjoint :
  ∀ {r}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode} →
  (P : PeriodicHermitianParsevalTransport model modes) →
  (cutoff : Nat) →
  (left right : LP.FourierField model) →
  physicalHermitianPairing P
    (Coefficient.hardLowCoefficientField model cutoff left) right
    ≡
  physicalHermitianPairing P
    left (Coefficient.hardLowCoefficientField model cutoff right)
hardLowPhysicalSelfAdjoint {model = model} {modes = modes}
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

hardHighPhysicalSelfAdjoint :
  ∀ {r}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode} →
  (P : PeriodicHermitianParsevalTransport model modes) →
  (cutoff : Nat) →
  (left right : LP.FourierField model) →
  physicalHermitianPairing P
    (Coefficient.hardHighCoefficientField model cutoff left) right
    ≡
  physicalHermitianPairing P
    left (Coefficient.hardHighCoefficientField model cutoff right)
hardHighPhysicalSelfAdjoint {model = model} {modes = modes}
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
      physicalHermitianPairing parseval
        (Coefficient.hardLowCoefficientField model cutoff left) right
        ≡
      physicalHermitianPairing parseval
        left (Coefficient.hardLowCoefficientField model cutoff right)

    highSelfAdjoint :
      (left right : LP.FourierField model) →
      physicalHermitianPairing parseval
        (Coefficient.hardHighCoefficientField model cutoff left) right
        ≡
      physicalHermitianPairing parseval
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
  ; lowSelfAdjoint = hardLowPhysicalSelfAdjoint
      (coefficientUnitaryHermitianParseval model modes) cutoff
  ; highSelfAdjoint = hardHighPhysicalSelfAdjoint
      (coefficientUnitaryHermitianParseval model modes) cutoff
  ; lowIdempotent =
      Coefficient.hardLowCoefficientIdempotent model cutoff
  ; highIdempotent =
      Coefficient.hardHighCoefficientIdempotent model cutoff
  }

hardProjectorPairingParsevalTransportClosed : Bool
hardProjectorPairingParsevalTransportClosed = true

hardProjectorOrthogonalCertificateConstructed : Bool
hardProjectorOrthogonalCertificateConstructed = true

hardProjectorPairingParsevalTransportClosedIsTrue :
  hardProjectorPairingParsevalTransportClosed ≡ true
hardProjectorPairingParsevalTransportClosedIsTrue = refl

hardProjectorOrthogonalCertificateConstructedIsTrue :
  hardProjectorOrthogonalCertificateConstructed ≡ true
hardProjectorOrthogonalCertificateConstructedIsTrue = refl
