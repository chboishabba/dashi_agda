module DASHI.Biology.OperatorStructureAdmissionBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Structure-first operator admission returned from Aristotle:
--   Lean/Spine/Duality.lean
--
-- The archive proves the real linear-algebra theorem that every alternating
-- form in odd dimension is degenerate, hence its concrete five-dimensional
-- carrier cannot be promoted to symplectic/Hamiltonian structure.  This Agda
-- owner does not pretend to reprove that continuum matrix theorem.  It makes
-- the theorem's admission consequence executable: a Hamiltonian promotion must
-- carry an explicit even-dimensional phase-space certificate rather than only
-- a scalar objective called an energy.

evenDimension : Nat → Bool
evenDimension zero = true
evenDimension (suc zero) = false
evenDimension (suc (suc n)) = evenDimension n

fiveDimensionIsNotEven : evenDimension 5 ≡ false
fiveDimensionIsNotEven = refl

fiveDimensionCannotCarryEvenCertificate :
  evenDimension 5 ≡ true → ⊥
fiveDimensionCannotCarryEvenCertificate ()

record ObjectiveCarrier : Set where
  constructor objectiveCarrier
  field
    stateCount : Nat
    objectiveValue : Nat

open ObjectiveCarrier public

record SymplecticAdmission : Set where
  constructor symplecticAdmission
  field
    dimension : Nat
    evenPhaseSpace : evenDimension dimension ≡ true
    nondegenerateAlternatingStructureSupplied : Bool
    nondegenerateAlternatingStructureCertificate :
      nondegenerateAlternatingStructureSupplied ≡ true

open SymplecticAdmission public

record HamiltonianAdmission : Set where
  constructor hamiltonianAdmission
  field
    phaseSpace : SymplecticAdmission
    hamiltonianValue : Nat
    dynamicsSupplied : Bool
    dynamicsCertificate : dynamicsSupplied ≡ true

open HamiltonianAdmission public

record FiveDimensionalHamiltonianAdmission : Set where
  constructor fiveDimensionalHamiltonianAdmission
  field
    fiveEvenCertificate : evenDimension 5 ≡ true

open FiveDimensionalHamiltonianAdmission public

noFiveDimensionalHamiltonianAdmission :
  FiveDimensionalHamiltonianAdmission → ⊥
noFiveDimensionalHamiltonianAdmission h =
  fiveDimensionCannotCarryEvenCertificate (fiveEvenCertificate h)

canonicalObjectiveOnly : ObjectiveCarrier
canonicalObjectiveOnly = objectiveCarrier 5 3

record OperatorAdmissionBoundary : Set where
  constructor operatorAdmissionBoundary
  field
    scalarObjectiveAloneIsHamiltonianSystem : Bool
    scalarObjectiveAloneIsHamiltonianSystemIsFalse :
      scalarObjectiveAloneIsHamiltonianSystem ≡ false

    oddDimensionalCarrierAutomaticallyHasSymplecticStructure : Bool
    oddDimensionalCarrierAutomaticallyHasSymplecticStructureIsFalse :
      oddDimensionalCarrierAutomaticallyHasSymplecticStructure ≡ false

    operatorNameSuppliesRequiredMathematicalStructure : Bool
    operatorNameSuppliesRequiredMathematicalStructureIsFalse :
      operatorNameSuppliesRequiredMathematicalStructure ≡ false

canonicalOperatorAdmissionBoundary : OperatorAdmissionBoundary
canonicalOperatorAdmissionBoundary =
  operatorAdmissionBoundary false refl false refl false refl
