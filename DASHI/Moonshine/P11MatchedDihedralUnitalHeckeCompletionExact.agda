module DASHI.Moonshine.P11MatchedDihedralUnitalHeckeCompletionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
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
-- Strengthen the split-lift no-go.  Even the full unital Hecke polynomial
-- relations can be engineered through a lossy representation quotient if one
-- puts a compatible Hecke character on the kernel.
--
-- Let P=s Phi and Q=I-P.  Using the level-11 newform coefficients
--
--   a2=-2, a3=-1, a5=1,
--   a4=2,  a9=-2, a25=-4,
--
-- define
--
--   R_n = s B_n Phi + a_n Q.
--
-- Then the prime operators still intertwine with the Brandt operators, their
-- coprime products commute, and the prime-square relations hold with the FULL
-- fine identity:
--
--   R2^2 = R4  + 2 I,
--   R3^2 = R9  + 3 I,
--   R5^2 = R25 + 5 I.
--
-- Therefore even "one simultaneous unital Hecke algebra exists" is not enough
-- to identify the desired representation-side correspondence.
--
-- Crucially, the constructed R2 sends an erased matched-sector basis state to
-- -2 times itself.  It is therefore not a nonnegative multiplicity/adjacency
-- correspondence.  Positivity/source-native geometric action is an essential
-- extra producer constraint, not optional decoration.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11
import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact as Brandt
import DASHI.Moonshine.P11BrandtJointHeckeAlgebraExact as Joint
import DASHI.Moonshine.P11BrandtPrimePowerHeckeExact as Power
import DASHI.Moonshine.P11MatchedDihedralSplitLiftNoGoExact as Lift
import DASHI.Moonshine.P11MatchedDihedralSixSectorBasisExact as Basis

------------------------------------------------------------------------
-- Kernel residual Q = I - P.
------------------------------------------------------------------------

subSectorVector :
  Lift.P11MatchedSectorVector →
  Lift.P11MatchedSectorVector →
  Lift.P11MatchedSectorVector
subSectorVector u v =
  Lift.sectorVector
    (Lift.epsilon u -ℤ Lift.epsilon v)
    (Lift.rho1 u -ℤ Lift.rho1 v)
    (Lift.rho2 u -ℤ Lift.rho2 v)
    (Lift.rho3 u -ℤ Lift.rho3 v)
    (Lift.rho4 u -ℤ Lift.rho4 v)
    (Lift.rho5 u -ℤ Lift.rho5 v)

kernelResidual : Lift.P11MatchedSectorVector → Lift.P11MatchedSectorVector
kernelResidual v = subSectorVector v (Lift.splitProjector v)

kernelResidualProjectsToZero :
  (v : Lift.P11MatchedSectorVector) →
  Lift.testProjection (kernelResidual v) ≡ P11.intPair (+ 0) (+ 0)
kernelResidualProjectsToZero (Lift.sectorVector e a b c d f) = refl

projectorPlusResidualIsIdentity :
  (v : Lift.P11MatchedSectorVector) →
  Lift.addSectorVector (Lift.splitProjector v) (kernelResidual v) ≡ v
projectorPlusResidualIsIdentity (Lift.sectorVector e a b c d f) = refl

------------------------------------------------------------------------
-- Unital Hecke completion by a scalar kernel character.
------------------------------------------------------------------------

completedLift :
  Brandt.P11BrandtMatrix → ℤ →
  Lift.P11MatchedSectorVector → Lift.P11MatchedSectorVector
completedLift B eigenvalue v =
  Lift.addSectorVector
    (Lift.splitLift B v)
    (Lift.scaleSectorVector eigenvalue (kernelResidual v))

completedLiftIntertwines :
  (B : Brandt.P11BrandtMatrix) →
  (eigenvalue : ℤ) →
  (v : Lift.P11MatchedSectorVector) →
  Lift.testProjection (completedLift B eigenvalue v)
  ≡ Brandt.matrixAction B (Lift.testProjection v)
completedLiftIntertwines B eigenvalue (Lift.sectorVector e a b c d f) = refl

------------------------------------------------------------------------
-- Prime and composite operators.
------------------------------------------------------------------------

R2 R3 R5 R6 R10 R15 R4 R9 R25 :
  Lift.P11MatchedSectorVector → Lift.P11MatchedSectorVector

R2 = completedLift Brandt.B11_2 (-[1+ 1 ])
R3 = completedLift Brandt.B11_3 (-[1+ 0 ])
R5 = completedLift Brandt.B11_5 (+ 1)

R6 = completedLift Joint.B11_6 (+ 2)
R10 = completedLift Joint.B11_10 (-[1+ 1 ])
R15 = completedLift Joint.B11_15 (-[1+ 0 ])

R4 = completedLift Joint.fullT4Matrix (+ 2)
R9 = completedLift Power.B11_9 (-[1+ 1 ])
R25 = completedLift Power.B11_25 (-[1+ 3 ])

------------------------------------------------------------------------
-- Exact simultaneous Brandt intertwining.
------------------------------------------------------------------------

R2Intertwines :
  (v : Lift.P11MatchedSectorVector) →
  Lift.testProjection (R2 v)
  ≡ Brandt.matrixAction Brandt.B11_2 (Lift.testProjection v)
R2Intertwines = completedLiftIntertwines Brandt.B11_2 (-[1+ 1 ])

R3Intertwines :
  (v : Lift.P11MatchedSectorVector) →
  Lift.testProjection (R3 v)
  ≡ Brandt.matrixAction Brandt.B11_3 (Lift.testProjection v)
R3Intertwines = completedLiftIntertwines Brandt.B11_3 (-[1+ 0 ])

R5Intertwines :
  (v : Lift.P11MatchedSectorVector) →
  Lift.testProjection (R5 v)
  ≡ Brandt.matrixAction Brandt.B11_5 (Lift.testProjection v)
R5Intertwines = completedLiftIntertwines Brandt.B11_5 (+ 1)

------------------------------------------------------------------------
-- Coprime Hecke products hold upstairs as well.
------------------------------------------------------------------------

R2R3IsR6 : (v : Lift.P11MatchedSectorVector) → R2 (R3 v) ≡ R6 v
R2R3IsR6 (Lift.sectorVector e a b c d f) = refl

R3R2IsR6 : (v : Lift.P11MatchedSectorVector) → R3 (R2 v) ≡ R6 v
R3R2IsR6 (Lift.sectorVector e a b c d f) = refl

R2R5IsR10 : (v : Lift.P11MatchedSectorVector) → R2 (R5 v) ≡ R10 v
R2R5IsR10 (Lift.sectorVector e a b c d f) = refl

R5R2IsR10 : (v : Lift.P11MatchedSectorVector) → R5 (R2 v) ≡ R10 v
R5R2IsR10 (Lift.sectorVector e a b c d f) = refl

R3R5IsR15 : (v : Lift.P11MatchedSectorVector) → R3 (R5 v) ≡ R15 v
R3R5IsR15 (Lift.sectorVector e a b c d f) = refl

R5R3IsR15 : (v : Lift.P11MatchedSectorVector) → R5 (R3 v) ≡ R15 v
R5R3IsR15 (Lift.sectorVector e a b c d f) = refl

------------------------------------------------------------------------
-- Full unital prime-square relations.
------------------------------------------------------------------------

R2PrimeSquareUnital :
  (v : Lift.P11MatchedSectorVector) →
  R2 (R2 v)
  ≡ Lift.addSectorVector (R4 v) (Lift.scaleSectorVector (+ 2) v)
R2PrimeSquareUnital (Lift.sectorVector e a b c d f) = refl

R3PrimeSquareUnital :
  (v : Lift.P11MatchedSectorVector) →
  R3 (R3 v)
  ≡ Lift.addSectorVector (R9 v) (Lift.scaleSectorVector (+ 3) v)
R3PrimeSquareUnital (Lift.sectorVector e a b c d f) = refl

R5PrimeSquareUnital :
  (v : Lift.P11MatchedSectorVector) →
  R5 (R5 v)
  ≡ Lift.addSectorVector (R25 v) (Lift.scaleSectorVector (+ 5) v)
R5PrimeSquareUnital (Lift.sectorVector e a b c d f) = refl

------------------------------------------------------------------------
-- But the completion is not a nonnegative multiplicity correspondence.
------------------------------------------------------------------------

R2OnErasedActualRho2 :
  R2 Basis.rho2Basis
  ≡ Lift.sectorVector (+ 0) (+ 0) (-[1+ 1 ]) (+ 0) (+ 0) (+ 0)
R2OnErasedActualRho2 = refl

record NonnegativeSectorVector : Set where
  field
    vector : Lift.P11MatchedSectorVector
    -- This tranche does not introduce a full integer-order cone API; the
    -- concrete negative coordinate below is enough to refute a Nat-valued
    -- multiplicity interpretation for this R2 completion.

R2CompletionHasNegativeMultiplicityWitness : Set
R2CompletionHasNegativeMultiplicityWitness =
  R2 Basis.rho2Basis
  ≡ Lift.sectorVector (+ 0) (+ 0) (-[1+ 1 ]) (+ 0) (+ 0) (+ 0)

r2CompletionNegativeWitness : R2CompletionHasNegativeMultiplicityWitness
r2CompletionNegativeWitness = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record P11MatchedDihedralUnitalCompletionBoundary : Set where
  field
    simultaneousPrimeIntertwinersConstructed : Bool
    simultaneousPrimeIntertwinersConstructedIsTrue :
      simultaneousPrimeIntertwinersConstructed ≡ true

    coprimeHeckeProductsConstructedUpstairs : Bool
    coprimeHeckeProductsConstructedUpstairsIsTrue :
      coprimeHeckeProductsConstructedUpstairs ≡ true

    fullIdentityPrimeSquareRelationsConstructed : Bool
    fullIdentityPrimeSquareRelationsConstructedIsTrue :
      fullIdentityPrimeSquareRelationsConstructed ≡ true

    constructionUsesIndependentKernelHeckeCharacter : Bool
    constructionUsesIndependentKernelHeckeCharacterIsTrue :
      constructionUsesIndependentKernelHeckeCharacter ≡ true

    ell2OperatorHasNegativeSectorCoefficient : Bool
    ell2OperatorHasNegativeSectorCoefficientIsTrue :
      ell2OperatorHasNegativeSectorCoefficient ≡ true

    completionPromotedToNonnegativeGeometricCorrespondence : Bool
    completionPromotedToNonnegativeGeometricCorrespondenceIsFalse :
      completionPromotedToNonnegativeGeometricCorrespondence ≡ false

    jointUnitalHeckeAlgebraAloneIdentifiesRepresentationAction : Bool
    jointUnitalHeckeAlgebraAloneIdentifiesRepresentationActionIsFalse :
      jointUnitalHeckeAlgebraAloneIdentifiesRepresentationAction ≡ false

canonicalP11MatchedDihedralUnitalCompletionBoundary :
  P11MatchedDihedralUnitalCompletionBoundary
canonicalP11MatchedDihedralUnitalCompletionBoundary =
  record
    { simultaneousPrimeIntertwinersConstructed = true
    ; simultaneousPrimeIntertwinersConstructedIsTrue = refl
    ; coprimeHeckeProductsConstructedUpstairs = true
    ; coprimeHeckeProductsConstructedUpstairsIsTrue = refl
    ; fullIdentityPrimeSquareRelationsConstructed = true
    ; fullIdentityPrimeSquareRelationsConstructedIsTrue = refl
    ; constructionUsesIndependentKernelHeckeCharacter = true
    ; constructionUsesIndependentKernelHeckeCharacterIsTrue = refl
    ; ell2OperatorHasNegativeSectorCoefficient = true
    ; ell2OperatorHasNegativeSectorCoefficientIsTrue = refl
    ; completionPromotedToNonnegativeGeometricCorrespondence = false
    ; completionPromotedToNonnegativeGeometricCorrespondenceIsFalse = refl
    ; jointUnitalHeckeAlgebraAloneIdentifiesRepresentationAction = false
    ; jointUnitalHeckeAlgebraAloneIdentifiesRepresentationActionIsFalse = refl
    }
