module DASHI.Physics.Closure.NSTriadKNHardProjectorCoefficientSelfAdjointExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011. DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Instantiate the finite diagonal-multiplier theorem on the repository's
-- literal periodic C^3 Fourier carrier.  The hard low/high projectors are the
-- 0/1 selectors already used by the exact LP/Bony modules.  Their coefficient
-- Hermitian self-adjointness is therefore a finite theorem, independent of
-- Parseval or a continuum function-space realization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNFiniteHermitianDiagonalMultiplierExact as Finite
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPeriodicHardProjectorAlgebraExact as Hard

complex3HermitianPairing :
  ∀ {r} (F : C3.RealField r) →
  Finite.FiniteHermitianPairing (C3.Complex3 F) (C3.Complex F)
complex3HermitianPairing F = record
  { zero = C3.complexZero F
  ; add = C3.complexAdd
  ; pair = C3.hermitianPairing3
  }

hardLowCoefficientField :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  Nat → LP.FourierField model → LP.FourierField model
hardLowCoefficientField model cutoff =
  Finite.diagonalField (LP.lowSelect model cutoff)

hardHighCoefficientField :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  Nat → LP.FourierField model → LP.FourierField model
hardHighCoefficientField model cutoff =
  Finite.diagonalField
    (λ mode → Hard.not (LP.lowSelect model cutoff mode))

hardLowCoefficientFieldMatchesLiteralProjector :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (field : LP.FourierField model) →
  (mode : Z3.FourierMode) →
  hardLowCoefficientField model cutoff field mode
    ≡ LP.lowProjector model cutoff field mode
hardLowCoefficientFieldMatchesLiteralProjector model cutoff field mode
  with LP.lowSelect model cutoff mode
... | true = refl
... | false = refl

hardHighCoefficientFieldMatchesLiteralProjector :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (field : LP.FourierField model) →
  (mode : Z3.FourierMode) →
  hardHighCoefficientField model cutoff field mode
    ≡ Hard.highProjector model cutoff field mode
hardHighCoefficientFieldMatchesLiteralProjector model cutoff field mode
  with LP.lowSelect model cutoff mode
... | true = refl
... | false = refl

coefficientHermitianPairing :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  List Z3.FourierMode →
  LP.FourierField model →
  LP.FourierField model →
  C3.Complex (LP.realField model)
coefficientHermitianPairing model modes =
  Finite.finiteHermitianPairing
    (complex3HermitianPairing (LP.realField model))
    modes

hardLowCoefficientSelfAdjoint :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (modes : List Z3.FourierMode) →
  (cutoff : Nat) →
  (left right : LP.FourierField model) →
  coefficientHermitianPairing model modes
    (hardLowCoefficientField model cutoff left) right
    ≡
  coefficientHermitianPairing model modes
    left (hardLowCoefficientField model cutoff right)
hardLowCoefficientSelfAdjoint model modes cutoff left right =
  Finite.finiteDiagonalMultiplierSelfAdjoint
    (complex3HermitianPairing (LP.realField model))
    modes
    (LP.lowSelect model cutoff)
    left right

hardHighCoefficientSelfAdjoint :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (modes : List Z3.FourierMode) →
  (cutoff : Nat) →
  (left right : LP.FourierField model) →
  coefficientHermitianPairing model modes
    (hardHighCoefficientField model cutoff left) right
    ≡
  coefficientHermitianPairing model modes
    left (hardHighCoefficientField model cutoff right)
hardHighCoefficientSelfAdjoint model modes cutoff left right =
  Finite.finiteDiagonalMultiplierSelfAdjoint
    (complex3HermitianPairing (LP.realField model))
    modes
    (λ mode → Hard.not (LP.lowSelect model cutoff mode))
    left right

hardLowCoefficientIdempotent :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (field : LP.FourierField model) →
  (mode : Z3.FourierMode) →
  hardLowCoefficientField model cutoff
    (hardLowCoefficientField model cutoff field) mode
    ≡ hardLowCoefficientField model cutoff field mode
hardLowCoefficientIdempotent model cutoff field mode =
  Finite.diagonalProjectIdempotent
    (LP.lowSelect model cutoff mode)
    (field mode)

hardHighCoefficientIdempotent :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (cutoff : Nat) →
  (field : LP.FourierField model) →
  (mode : Z3.FourierMode) →
  hardHighCoefficientField model cutoff
    (hardHighCoefficientField model cutoff field) mode
    ≡ hardHighCoefficientField model cutoff field mode
hardHighCoefficientIdempotent model cutoff field mode =
  Finite.diagonalProjectIdempotent
    (Hard.not (LP.lowSelect model cutoff mode))
    (field mode)

hardProjectorCoefficientSelfAdjointnessClosed : Bool
hardProjectorCoefficientSelfAdjointnessClosed = true

hardProjectorCoefficientIdempotenceClosed : Bool
hardProjectorCoefficientIdempotenceClosed = true

hardProjectorCoefficientSelfAdjointnessClosedIsTrue :
  hardProjectorCoefficientSelfAdjointnessClosed ≡ true
hardProjectorCoefficientSelfAdjointnessClosedIsTrue = refl

hardProjectorCoefficientIdempotenceClosedIsTrue :
  hardProjectorCoefficientIdempotenceClosed ≡ true
hardProjectorCoefficientIdempotenceClosedIsTrue = refl
