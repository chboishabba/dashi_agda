module DASHI.Physics.Chemistry.AtomicPeriodicTable369P2CoulombExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369ExteriorC3RepresentationExact as Exterior

------------------------------------------------------------------------
-- Exact execution receipt for the projected electron-electron Coulomb operator
-- on the selected common-spin hydrogenic 2p^2 antisymmetric orbital sector.
--
-- External-source role is unchanged from the parent atomic tranche:
-- NIST DLMF supplies the standard hydrogenic radial-function authority.  The
-- multipole/Gaunt composition and exact symbolic integration are DASHI-owned
-- reconstruction/execution, not experimental authority and not a 369 ontology.
------------------------------------------------------------------------

record Rational : Set where
  constructor rational
  field
    numerator : Nat
    denominator : Nat

open Rational public

zeroRational : Rational
zeroRational = rational 0 1

p2CoulombEnergy : Rational
p2CoulombEnergy = rational 21 128

slaterF0 : Rational
slaterF0 = rational 93 512

slaterF2 : Rational
slaterF2 = rational 45 512

producerPath : String
producerPath = "scripts/atomic_369_p2_coulomb_exact.py"

receiptPath : String
receiptPath = "generated/atomic_369_p2_coulomb_receipt.json"

data P2Basis : Set where
  p2NegZero : P2Basis
  p2NegPos : P2Basis
  p2ZeroPos : P2Basis

p2C3Step : P2Basis -> P2Basis
p2C3Step p2NegZero = p2ZeroPos
p2C3Step p2NegPos = p2NegZero
p2C3Step p2ZeroPos = p2NegPos

p2C3StepOrderThree :
  (x : P2Basis) ->
  p2C3Step (p2C3Step (p2C3Step x)) ≡ x
p2C3StepOrderThree p2NegZero = refl
p2C3StepOrderThree p2NegPos = refl
p2C3StepOrderThree p2ZeroPos = refl

-- Matrix values are encoded on the canonical unsigned basis.  The actual
-- exterior action carries signs; because V_ee is scalar on this sector, the
-- sign bookkeeping cannot break commutation.
coulombMatrixElement : P2Basis -> P2Basis -> Rational
coulombMatrixElement p2NegZero p2NegZero = p2CoulombEnergy
coulombMatrixElement p2NegZero p2NegPos = zeroRational
coulombMatrixElement p2NegZero p2ZeroPos = zeroRational
coulombMatrixElement p2NegPos p2NegZero = zeroRational
coulombMatrixElement p2NegPos p2NegPos = p2CoulombEnergy
coulombMatrixElement p2NegPos p2ZeroPos = zeroRational
coulombMatrixElement p2ZeroPos p2NegZero = zeroRational
coulombMatrixElement p2ZeroPos p2NegPos = zeroRational
coulombMatrixElement p2ZeroPos p2ZeroPos = p2CoulombEnergy

coulombMatrixIsC3Invariant :
  (a b : P2Basis) ->
  coulombMatrixElement (p2C3Step a) (p2C3Step b)
  ≡ coulombMatrixElement a b
coulombMatrixIsC3Invariant p2NegZero p2NegZero = refl
coulombMatrixIsC3Invariant p2NegZero p2NegPos = refl
coulombMatrixIsC3Invariant p2NegZero p2ZeroPos = refl
coulombMatrixIsC3Invariant p2NegPos p2NegZero = refl
coulombMatrixIsC3Invariant p2NegPos p2NegPos = refl
coulombMatrixIsC3Invariant p2NegPos p2ZeroPos = refl
coulombMatrixIsC3Invariant p2ZeroPos p2NegZero = refl
coulombMatrixIsC3Invariant p2ZeroPos p2NegPos = refl
coulombMatrixIsC3Invariant p2ZeroPos p2ZeroPos = refl

------------------------------------------------------------------------
-- Typed relationship to the finite exterior basis.  This is a basis chart,
-- not a claim that the whole atomic Fock space has been constructed.
------------------------------------------------------------------------

p2BasisOfWedge : Exterior.Wedge2Basis -> P2Basis
p2BasisOfWedge Exterior.wedgeNegZero = p2NegZero
p2BasisOfWedge Exterior.wedgeNegPos = p2NegPos
p2BasisOfWedge Exterior.wedgeZeroPos = p2ZeroPos

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record P2CoulombExecutionBoundary : Set where
  constructor p2CoulombExecutionBoundary
  field
    hydrogenic2pRadialSourceRoleRetained : Bool
    exactSlaterF0Paid : Bool
    exactSlaterF2Paid : Bool
    exactGauntProjectionPaid : Bool
    projectedCoulombMatrixScalarPaid : Bool
    interactionSensitiveC3CommutationPaid : Bool
    commonSpinAntisymmetricP2ScopeExplicit : Bool

    completeAtomicHamiltonianPaid : Bool
    spinOrbitPaid : Bool
    correlationOutsideSelectedP2SectorPaid : Bool
    empiricalSpectroscopyPaidHere : Bool
    fullAtom369IdentityPaid : Bool

open P2CoulombExecutionBoundary public

canonicalP2CoulombExecutionBoundary : P2CoulombExecutionBoundary
canonicalP2CoulombExecutionBoundary =
  p2CoulombExecutionBoundary
    true true true true true true true
    false false false false false

fullAtom369IdentityPaidIsFalse :
  fullAtom369IdentityPaid canonicalP2CoulombExecutionBoundary ≡ false
fullAtom369IdentityPaidIsFalse = refl
