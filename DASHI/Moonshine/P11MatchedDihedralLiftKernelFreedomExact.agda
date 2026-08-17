module DASHI.Moonshine.P11MatchedDihedralLiftKernelFreedomExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- This is finite linear algebra internal to DASHI.  The representation and
-- Hecke vocabulary follows Fulton--Harris and Miyake as cited by the imported
-- producer modules; no additional external theorem is claimed here.
--
-- DASHI CONTRIBUTION
--
-- Make the underdetermination of backwards intertwiner solving explicit.
-- The split test projection Phi has a nonzero kernel.  Therefore any fine
-- operator K with Phi K = 0 can be added to a mechanical lift without changing
-- its coarse Brandt image:
--
--   Phi (R_B + K) = B Phi.
--
-- We construct one literal nonzero K and hence two distinct simultaneous
-- families lifting B_11(2), B_11(3), B_11(5).  This proves that simultaneous
-- intertwining alone does not identify a representation-side Hecke action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (+_)

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11
import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact as Brandt
import DASHI.Moonshine.P11MatchedDihedralSplitLiftNoGoExact as Lift
import DASHI.Moonshine.P11MatchedDihedralSixSectorBasisExact as Basis

------------------------------------------------------------------------
-- A nonzero endomorphism whose image lies in ker Phi.
------------------------------------------------------------------------

kernelPerturbation :
  Lift.P11MatchedSectorVector → Lift.P11MatchedSectorVector
kernelPerturbation v =
  Lift.scaleSectorVector (Lift.epsilon v) Lift.kernelWitness

kernelPerturbationProjectsToZero :
  (v : Lift.P11MatchedSectorVector) →
  Lift.testProjection (kernelPerturbation v)
  ≡ P11.intPair (+ 0) (+ 0)
kernelPerturbationProjectsToZero (Lift.sectorVector e a b c d f) = refl

kernelPerturbationIsNonzeroOnSinglet :
  kernelPerturbation Basis.epsilonBasis ≡ Lift.zeroSectorVector → ⊥
kernelPerturbationIsNonzeroOnSinglet = Lift.kernelWitnessIsNonzero

------------------------------------------------------------------------
-- Alternative lift of any Brandt matrix.
------------------------------------------------------------------------

alternativeLift :
  Brandt.P11BrandtMatrix →
  Lift.P11MatchedSectorVector →
  Lift.P11MatchedSectorVector
alternativeLift B v =
  Lift.addSectorVector (Lift.splitLift B v) (kernelPerturbation v)

alternativeLiftIntertwines :
  (B : Brandt.P11BrandtMatrix) →
  (v : Lift.P11MatchedSectorVector) →
  Lift.testProjection (alternativeLift B v)
  ≡ Brandt.matrixAction B (Lift.testProjection v)
alternativeLiftIntertwines B (Lift.sectorVector e a b c d f) = refl

R2alt R3alt R5alt :
  Lift.P11MatchedSectorVector → Lift.P11MatchedSectorVector
R2alt = alternativeLift Brandt.B11_2
R3alt = alternativeLift Brandt.B11_3
R5alt = alternativeLift Brandt.B11_5

R2altIntertwines :
  (v : Lift.P11MatchedSectorVector) →
  Lift.testProjection (R2alt v)
  ≡ Brandt.matrixAction Brandt.B11_2 (Lift.testProjection v)
R2altIntertwines = alternativeLiftIntertwines Brandt.B11_2

R3altIntertwines :
  (v : Lift.P11MatchedSectorVector) →
  Lift.testProjection (R3alt v)
  ≡ Brandt.matrixAction Brandt.B11_3 (Lift.testProjection v)
R3altIntertwines = alternativeLiftIntertwines Brandt.B11_3

R5altIntertwines :
  (v : Lift.P11MatchedSectorVector) →
  Lift.testProjection (R5alt v)
  ≡ Brandt.matrixAction Brandt.B11_5 (Lift.testProjection v)
R5altIntertwines = alternativeLiftIntertwines Brandt.B11_5

------------------------------------------------------------------------
-- The alternative family is genuinely distinct from the split family.
------------------------------------------------------------------------

R2OnSinglet : Lift.R2 Basis.epsilonBasis ≡
  Lift.sectorVector (+ 0) (+ 2) (+ 0) (+ 0) (+ 0) (+ 0)
R2OnSinglet = refl

R2altOnSinglet : R2alt Basis.epsilonBasis ≡
  Lift.sectorVector (+ 0) (+ 3) (-[1+ 0 ]) (+ 0) (+ 0) (+ 0)
R2altOnSinglet = refl

R2altDiffersFromR2 :
  R2alt Basis.epsilonBasis ≡ Lift.R2 Basis.epsilonBasis → ⊥
R2altDiffersFromR2 ()

------------------------------------------------------------------------
-- The same coarse triple therefore has at least two simultaneous fine lifts.
-- No uniqueness/explanation theorem can follow from intertwining alone.
------------------------------------------------------------------------

record P11MatchedDihedralKernelFreedomBoundary : Set where
  field
    nonzeroKernelEndomorphismConstructed : Bool
    nonzeroKernelEndomorphismConstructedIsTrue :
      nonzeroKernelEndomorphismConstructed ≡ true

    secondSimultaneousPrimeLiftFamilyConstructed : Bool
    secondSimultaneousPrimeLiftFamilyConstructedIsTrue :
      secondSimultaneousPrimeLiftFamilyConstructed ≡ true

    secondFamilyHasSameCoarseBrandtImages : Bool
    secondFamilyHasSameCoarseBrandtImagesIsTrue :
      secondFamilyHasSameCoarseBrandtImages ≡ true

    secondFamilyProvablyDistinct : Bool
    secondFamilyProvablyDistinctIsTrue : secondFamilyProvablyDistinct ≡ true

    intertwinerExistenceDeterminesUniqueFineHeckeAction : Bool
    intertwinerExistenceDeterminesUniqueFineHeckeActionIsFalse :
      intertwinerExistenceDeterminesUniqueFineHeckeAction ≡ false

canonicalP11MatchedDihedralKernelFreedomBoundary :
  P11MatchedDihedralKernelFreedomBoundary
canonicalP11MatchedDihedralKernelFreedomBoundary =
  record
    { nonzeroKernelEndomorphismConstructed = true
    ; nonzeroKernelEndomorphismConstructedIsTrue = refl
    ; secondSimultaneousPrimeLiftFamilyConstructed = true
    ; secondSimultaneousPrimeLiftFamilyConstructedIsTrue = refl
    ; secondFamilyHasSameCoarseBrandtImages = true
    ; secondFamilyHasSameCoarseBrandtImagesIsTrue = refl
    ; secondFamilyProvablyDistinct = true
    ; secondFamilyProvablyDistinctIsTrue = refl
    ; intertwinerExistenceDeterminesUniqueFineHeckeAction = false
    ; intertwinerExistenceDeterminesUniqueFineHeckeActionIsFalse = refl
    }
