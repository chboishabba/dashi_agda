module DASHI.Physics.Chemistry.AmmoniaHamiltonianWavefunctionValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaHamiltonianWavefunctionExact as NH3

sameObjectSymbolicHamiltonianPaid :
  NH3.HamiltonianWavefunctionBoundary.sameObjectSymbolicHamiltonianExpressionPaid
    NH3.canonicalHamiltonianWavefunctionBoundary ≡ true
sameObjectSymbolicHamiltonianPaid = refl

energyValuedOperatorStillUnpaid :
  NH3.HamiltonianWavefunctionBoundary.energyValuedHamiltonianOperatorPaid
    NH3.canonicalHamiltonianWavefunctionBoundary ≡ false
energyValuedOperatorStillUnpaid = refl

sourceBackedGroundStatePESPaid :
  NH3.HamiltonianWavefunctionBoundary.sourceBackedGroundElectronicPESPaid
    NH3.canonicalHamiltonianWavefunctionBoundary ≡ true
sourceBackedGroundStatePESPaid = refl

occupationBasisStatePaid :
  NH3.HamiltonianWavefunctionBoundary.literalOccupationBasisStatePaid
    NH3.canonicalHamiltonianWavefunctionBoundary ≡ true
occupationBasisStatePaid = refl

tenOccupiedSpinOrbitals :
  NH3.NH3OccupationState.occupiedSpinOrbitalCount NH3.canonicalNH3OccupationState ≡ 10
tenOccupiedSpinOrbitals = refl

c3SymmetryAdapterPaid :
  NH3.HamiltonianWavefunctionBoundary.c3SymmetryAdapterPaid
    NH3.canonicalHamiltonianWavefunctionBoundary ≡ true
c3SymmetryAdapterPaid = refl

realSpaceCoefficientsStillUnpaid :
  NH3.HamiltonianWavefunctionBoundary.numericRealSpaceWavefunctionCoefficientsPaid
    NH3.canonicalHamiltonianWavefunctionBoundary ≡ false
realSpaceCoefficientsStillUnpaid = refl

hamiltonianDiagonalizationStillUnpaid :
  NH3.HamiltonianWavefunctionBoundary.numericHamiltonianDiagonalizationPaid
    NH3.canonicalHamiltonianWavefunctionBoundary ≡ false
hamiltonianDiagonalizationStillUnpaid = refl
