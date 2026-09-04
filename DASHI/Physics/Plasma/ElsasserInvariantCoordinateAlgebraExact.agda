module DASHI.Physics.Plasma.ElsasserInvariantCoordinateAlgebraExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

------------------------------------------------------------------------
-- ELSASSER INVARIANT COORDINATE ALGEBRA
--
-- Division-free exact identities for one scalar mode coordinate:
--   z+ = u + b
--   z- = u - b
--
--   2 (u^2 + b^2) = (z+)^2 + (z-)^2
--   4 u b           = (z+)^2 - (z-)^2
--
-- These are chart identities only.  They do not prove any dynamical
-- conservation theorem.
------------------------------------------------------------------------

private
  sq : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F
  sq {F = F} x = C3.multiply F x x

  sub : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

  two four : ∀ {r} {F : C3.RealField r} → C3.Carrier F
  two {F = F} = C3.add F (C3.one F) (C3.one F)
  four {F = F} = C3.add F two two

zPlus : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
zPlus {F = F} u b = C3.add F u b

zMinus : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
zMinus {F = F} u b = sub u b

physicalEnergyCoordinate : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
physicalEnergyCoordinate {F = F} u b = C3.add F (sq u) (sq b)

crossHelicityCoordinate : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
crossHelicityCoordinate {F = F} u b = C3.multiply F u b

plusEnergyCoordinate : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
plusEnergyCoordinate u b = sq (zPlus u b)

minusEnergyCoordinate : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
minusEnergyCoordinate u b = sq (zMinus u b)

energyElsasserDivisionFree :
  ∀ {r} {F : C3.RealField r} (u b : C3.Carrier F) →
  C3.multiply F two (physicalEnergyCoordinate u b)
  ≡ C3.add F (plusEnergyCoordinate u b) (minusEnergyCoordinate u b)
energyElsasserDivisionFree {F = F} u b =
  R.solve 2
    (λ u b →
      ((R.Κ two R.⊗ ((u R.⊗ u) R.⊕ (b R.⊗ b)))
      R.⊜
      (((u R.⊕ b) R.⊗ (u R.⊕ b))
        R.⊕ ((u R.⊕ (R.⊝ b)) R.⊗ (u R.⊕ (R.⊝ b)))))
    refl u b
  where module R = Field.Solver F

crossHelicityElsasserDivisionFree :
  ∀ {r} {F : C3.RealField r} (u b : C3.Carrier F) →
  C3.multiply F four (crossHelicityCoordinate u b)
  ≡ sub (plusEnergyCoordinate u b) (minusEnergyCoordinate u b)
crossHelicityElsasserDivisionFree {F = F} u b =
  R.solve 2
    (λ u b →
      ((R.Κ four R.⊗ (u R.⊗ b))
      R.⊜
      (((u R.⊕ b) R.⊗ (u R.⊕ b))
        R.⊕ (R.⊝ ((u R.⊕ (R.⊝ b)) R.⊗ (u R.⊕ (R.⊝ b))))))
    refl u b
  where module R = Field.Solver F

record ElsasserInvariantCoordinateBoundary : Set where
  constructor elsasser-invariant-coordinate-boundary
  field
    energyAndCrossHelicityAreSameObserver : Bool
    energyAndCrossHelicityAreSameObserverIsFalse :
      energyAndCrossHelicityAreSameObserver ≡ false

    chartIdentityProvesDynamicalConservation : Bool
    chartIdentityProvesDynamicalConservationIsFalse :
      chartIdentityProvesDynamicalConservation ≡ false

    plusMinusEnergyCoordinatesJointlyRecoverBothQuadraticObservers : Bool
    plusMinusEnergyCoordinatesJointlyRecoverBothQuadraticObserversIsTrue :
      plusMinusEnergyCoordinatesJointlyRecoverBothQuadraticObservers ≡ true

canonicalElsasserInvariantCoordinateBoundary : ElsasserInvariantCoordinateBoundary
canonicalElsasserInvariantCoordinateBoundary =
  elsasser-invariant-coordinate-boundary false refl false refl true refl
