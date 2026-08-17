module DASHI.Moonshine.P11MatchedDihedralSplitLiftNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- Falsifier-first analysis of the next representation/Brandt step at p=11.
-- Here j=5, so the existing matched-dihedral restriction has six occurring
-- sectors
--
--   epsilon, rho1, rho2, rho3, rho4, rho5,
--
-- while the geometric supersingular Brandt carrier has two states.
--
-- Any attempt to solve Phi R = B Phi backwards through a lossy split quotient
-- risks becoming tautological: given a projection Phi with a section s, one can
-- always manufacture the split lift
--
--   R_B = s B Phi.
--
-- It automatically intertwines and preserves multiplication, but its unit is
-- the projector P=s Phi rather than the identity on the fine carrier.  Thus a
-- weight-two prime-square relation downstairs
--
--   B_ell^2 = B_(ell^2) + ell I
--
-- lifts only to
--
--   R_ell^2 = R_(ell^2) + ell P,
--
-- not to the desired fine-carrier relation with ell I unless P=I.
--
-- The concrete split quotient below is deliberately only a countermodel:
-- singlet coordinate versus the sum of all five doublet coordinates.  It is NOT
-- promoted as the sought geometric Phi_11.  Its explicit kernel proves why
-- mere simultaneous intertwiner existence is too weak a success criterion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11
import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact as Brandt
import DASHI.Moonshine.P11BrandtJointHeckeAlgebraExact as Joint
import DASHI.Moonshine.P11BrandtPrimePowerHeckeExact as Power

------------------------------------------------------------------------
-- Six-coordinate free module matching the six occurring j=5 matched sectors.
------------------------------------------------------------------------

record P11MatchedSectorVector : Set where
  constructor sectorVector
  field
    epsilon rho1 rho2 rho3 rho4 rho5 : ℤ

open P11MatchedSectorVector public

zeroSectorVector : P11MatchedSectorVector
zeroSectorVector = sectorVector (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0)

addSectorVector :
  P11MatchedSectorVector → P11MatchedSectorVector → P11MatchedSectorVector
addSectorVector u v =
  sectorVector
    (epsilon u +ℤ epsilon v)
    (rho1 u +ℤ rho1 v)
    (rho2 u +ℤ rho2 v)
    (rho3 u +ℤ rho3 v)
    (rho4 u +ℤ rho4 v)
    (rho5 u +ℤ rho5 v)

scaleSectorVector : ℤ → P11MatchedSectorVector → P11MatchedSectorVector
scaleSectorVector scalar v =
  sectorVector
    (scalar *ℤ epsilon v)
    (scalar *ℤ rho1 v)
    (scalar *ℤ rho2 v)
    (scalar *ℤ rho3 v)
    (scalar *ℤ rho4 v)
    (scalar *ℤ rho5 v)

------------------------------------------------------------------------
-- Explicit split two-coordinate test projection.
------------------------------------------------------------------------

testProjection : P11MatchedSectorVector → P11.IntPair
testProjection v =
  P11.intPair
    (epsilon v)
    (rho1 v +ℤ rho2 v +ℤ rho3 v +ℤ rho4 v +ℤ rho5 v)

testSection : P11.IntPair → P11MatchedSectorVector
testSection coarse =
  sectorVector
    (P11.left coarse)
    (P11.right coarse)
    (+ 0) (+ 0) (+ 0) (+ 0)

testSectionRoundTrip :
  (coarse : P11.IntPair) →
  testProjection (testSection coarse) ≡ coarse
testSectionRoundTrip (P11.intPair left right) = refl

splitProjector : P11MatchedSectorVector → P11MatchedSectorVector
splitProjector = testSection ∘ testProjection

------------------------------------------------------------------------
-- The projection is genuinely lossy.
------------------------------------------------------------------------

kernelWitness : P11MatchedSectorVector
kernelWitness =
  sectorVector (+ 0) (+ 1) (-[1+ 0 ]) (+ 0) (+ 0) (+ 0)

kernelWitnessProjectsToZero :
  testProjection kernelWitness ≡ P11.intPair (+ 0) (+ 0)
kernelWitnessProjectsToZero = refl

kernelWitnessIsNonzero : kernelWitness ≡ zeroSectorVector → ⊥
kernelWitnessIsNonzero ()

rho2Basis : P11MatchedSectorVector
rho2Basis = sectorVector (+ 0) (+ 0) (+ 1) (+ 0) (+ 0) (+ 0)

projectorErasesRho2Basis : splitProjector rho2Basis ≡ zeroSectorVector
projectorErasesRho2Basis = refl

projectorIsNotIdentity :
  ((v : P11MatchedSectorVector) → splitProjector v ≡ v) → ⊥
projectorIsNotIdentity projectorIdentity =
  kernelWitnessIsNonzero
    (trans
      (sym (projectorIdentity kernelWitness))
      refl)

------------------------------------------------------------------------
-- Mechanical split lift of any two-state Brandt operator.
------------------------------------------------------------------------

splitLift : Brandt.P11BrandtMatrix → P11MatchedSectorVector → P11MatchedSectorVector
splitLift B fine = testSection (Brandt.matrixAction B (testProjection fine))

splitLiftIntertwines :
  (B : Brandt.P11BrandtMatrix) →
  (fine : P11MatchedSectorVector) →
  testProjection (splitLift B fine)
  ≡ Brandt.matrixAction B (testProjection fine)
splitLiftIntertwines B fine = testSectionRoundTrip _

R2 R3 R5 : P11MatchedSectorVector → P11MatchedSectorVector
R2 = splitLift Brandt.B11_2
R3 = splitLift Brandt.B11_3
R5 = splitLift Brandt.B11_5

R6 R10 R15 : P11MatchedSectorVector → P11MatchedSectorVector
R6 = splitLift Joint.B11_6
R10 = splitLift Joint.B11_10
R15 = splitLift Joint.B11_15

R9 R25 : P11MatchedSectorVector → P11MatchedSectorVector
R9 = splitLift Power.B11_9
R25 = splitLift Power.B11_25

------------------------------------------------------------------------
-- Exact simultaneous intertwining of the mechanically lifted prime family.
------------------------------------------------------------------------

R2Intertwines :
  (fine : P11MatchedSectorVector) →
  testProjection (R2 fine)
  ≡ Brandt.matrixAction Brandt.B11_2 (testProjection fine)
R2Intertwines = splitLiftIntertwines Brandt.B11_2

R3Intertwines :
  (fine : P11MatchedSectorVector) →
  testProjection (R3 fine)
  ≡ Brandt.matrixAction Brandt.B11_3 (testProjection fine)
R3Intertwines = splitLiftIntertwines Brandt.B11_3

R5Intertwines :
  (fine : P11MatchedSectorVector) →
  testProjection (R5 fine)
  ≡ Brandt.matrixAction Brandt.B11_5 (testProjection fine)
R5Intertwines = splitLiftIntertwines Brandt.B11_5

------------------------------------------------------------------------
-- Multiplication is preserved by the split construction because Phi s = I.
-- These exact equalities demonstrate why pairwise commutation alone still does
-- not make the lift explanatory.
------------------------------------------------------------------------

R2R3IsR6 :
  (fine : P11MatchedSectorVector) → R2 (R3 fine) ≡ R6 fine
R2R3IsR6 (sectorVector e a b c d f) = refl

R3R2IsR6 :
  (fine : P11MatchedSectorVector) → R3 (R2 fine) ≡ R6 fine
R3R2IsR6 (sectorVector e a b c d f) = refl

R2R5IsR10 :
  (fine : P11MatchedSectorVector) → R2 (R5 fine) ≡ R10 fine
R2R5IsR10 (sectorVector e a b c d f) = refl

R5R2IsR10 :
  (fine : P11MatchedSectorVector) → R5 (R2 fine) ≡ R10 fine
R5R2IsR10 (sectorVector e a b c d f) = refl

R3R5IsR15 :
  (fine : P11MatchedSectorVector) → R3 (R5 fine) ≡ R15 fine
R3R5IsR15 (sectorVector e a b c d f) = refl

R5R3IsR15 :
  (fine : P11MatchedSectorVector) → R5 (R3 fine) ≡ R15 fine
R5R3IsR15 (sectorVector e a b c d f) = refl

------------------------------------------------------------------------
-- Prime-square relations close on P=s Phi, not on the fine identity.
------------------------------------------------------------------------

R2SquaredUsesProjector :
  (fine : P11MatchedSectorVector) →
  R2 (R2 fine)
  ≡ addSectorVector (splitLift Joint.fullT4Matrix fine)
      (scaleSectorVector (+ 2) (splitProjector fine))
R2SquaredUsesProjector (sectorVector e a b c d f) = refl

R3SquaredUsesProjector :
  (fine : P11MatchedSectorVector) →
  R3 (R3 fine)
  ≡ addSectorVector (R9 fine)
      (scaleSectorVector (+ 3) (splitProjector fine))
R3SquaredUsesProjector (sectorVector e a b c d f) = refl

R5SquaredUsesProjector :
  (fine : P11MatchedSectorVector) →
  R5 (R5 fine)
  ≡ addSectorVector (R25 fine)
      (scaleSectorVector (+ 5) (splitProjector fine))
R5SquaredUsesProjector (sectorVector e a b c d f) = refl

------------------------------------------------------------------------
-- Concrete failure of the desired unital fine-carrier prime-square relation.
-- On rho2Basis every mechanical split lift vanishes after the first projection,
-- but ell * identity does not vanish.
------------------------------------------------------------------------

R3SquaredOnErasedBasis : R3 (R3 rho2Basis) ≡ zeroSectorVector
R3SquaredOnErasedBasis = refl

R9OnErasedBasis : R9 rho2Basis ≡ zeroSectorVector
R9OnErasedBasis = refl

threeIdentityOnErasedBasis :
  scaleSectorVector (+ 3) rho2Basis
  ≡ sectorVector (+ 0) (+ 0) (+ 3) (+ 0) (+ 0) (+ 0)
threeIdentityOnErasedBasis = refl

unitalR3PrimeSquareFailsOnErasedBasis :
  R3 (R3 rho2Basis)
  ≡ addSectorVector (R9 rho2Basis) (scaleSectorVector (+ 3) rho2Basis)
  → ⊥
unitalR3PrimeSquareFailsOnErasedBasis ()

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record P11MatchedDihedralSplitLiftBoundary : Set where
  field
    sixCoordinateMatchedSectorCarrierConstructed : Bool
    sixCoordinateMatchedSectorCarrierConstructedIsTrue :
      sixCoordinateMatchedSectorCarrierConstructed ≡ true

    explicitLossyTwoCoordinateProjectionConstructed : Bool
    explicitLossyTwoCoordinateProjectionConstructedIsTrue :
      explicitLossyTwoCoordinateProjectionConstructed ≡ true

    simultaneousBrandtIntertwinersMechanicallyConstructed : Bool
    simultaneousBrandtIntertwinersMechanicallyConstructedIsTrue :
      simultaneousBrandtIntertwinersMechanicallyConstructed ≡ true

    pairwiseHeckeProductsMechanicallyPreserved : Bool
    pairwiseHeckeProductsMechanicallyPreservedIsTrue :
      pairwiseHeckeProductsMechanicallyPreserved ≡ true

    primeSquareRelationsUseProjectorNotFineIdentity : Bool
    primeSquareRelationsUseProjectorNotFineIdentityIsTrue :
      primeSquareRelationsUseProjectorNotFineIdentity ≡ true

    explicitUnitalPrimeSquareFailureConstructed : Bool
    explicitUnitalPrimeSquareFailureConstructedIsTrue :
      explicitUnitalPrimeSquareFailureConstructed ≡ true

    testProjectionPromotedToGeometricPhi11 : Bool
    testProjectionPromotedToGeometricPhi11IsFalse :
      testProjectionPromotedToGeometricPhi11 ≡ false

    mereIntertwinerExistenceTreatedAsExplanation : Bool
    mereIntertwinerExistenceTreatedAsExplanationIsFalse :
      mereIntertwinerExistenceTreatedAsExplanation ≡ false

canonicalP11MatchedDihedralSplitLiftBoundary :
  P11MatchedDihedralSplitLiftBoundary
canonicalP11MatchedDihedralSplitLiftBoundary =
  record
    { sixCoordinateMatchedSectorCarrierConstructed = true
    ; sixCoordinateMatchedSectorCarrierConstructedIsTrue = refl
    ; explicitLossyTwoCoordinateProjectionConstructed = true
    ; explicitLossyTwoCoordinateProjectionConstructedIsTrue = refl
    ; simultaneousBrandtIntertwinersMechanicallyConstructed = true
    ; simultaneousBrandtIntertwinersMechanicallyConstructedIsTrue = refl
    ; pairwiseHeckeProductsMechanicallyPreserved = true
    ; pairwiseHeckeProductsMechanicallyPreservedIsTrue = refl
    ; primeSquareRelationsUseProjectorNotFineIdentity = true
    ; primeSquareRelationsUseProjectorNotFineIdentityIsTrue = refl
    ; explicitUnitalPrimeSquareFailureConstructed = true
    ; explicitUnitalPrimeSquareFailureConstructedIsTrue = refl
    ; testProjectionPromotedToGeometricPhi11 = false
    ; testProjectionPromotedToGeometricPhi11IsFalse = refl
    ; mereIntertwinerExistenceTreatedAsExplanation = false
    ; mereIntertwinerExistenceTreatedAsExplanationIsFalse = refl
    }
