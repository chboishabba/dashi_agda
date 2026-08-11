module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHodgeDiamondExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Claire Voisin,
-- "Hodge Theory and Complex Algebraic Geometry I".
-- DOI: 10.1017/CBO9780511615344.
--
-- DASHI CONTRIBUTION
--
-- Record and check the finite Hodge diamond of the complex projective line:
--
--   h^(0,0)=1, h^(1,1)=1,
--   h^(1,0)=h^(0,1)=0.
--
-- The exact table proves conjugation symmetry and Betti numbers b0=1, b1=0,
-- b2=1.  A separate geometric-identification record is required before this
-- finite table can be claimed as the cohomology of an implemented projective
-- variety; the table itself does not construct de Rham cohomology.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as H

data P1Bidegree : Set where
  degree00 degree10 degree01 degree11 : P1Bidegree

swapBidegree : P1Bidegree → P1Bidegree
swapBidegree degree00 = degree00
swapBidegree degree10 = degree01
swapBidegree degree01 = degree10
swapBidegree degree11 = degree11

swapBidegreeInvolutive : ∀ degree →
  swapBidegree (swapBidegree degree) ≡ degree
swapBidegreeInvolutive degree00 = refl
swapBidegreeInvolutive degree10 = refl
swapBidegreeInvolutive degree01 = refl
swapBidegreeInvolutive degree11 = refl

p1HodgeNumber : P1Bidegree → Nat
p1HodgeNumber degree00 = 1
p1HodgeNumber degree10 = 0
p1HodgeNumber degree01 = 0
p1HodgeNumber degree11 = 1

p1HodgeConjugationSymmetry : ∀ degree →
  p1HodgeNumber (swapBidegree degree) ≡ p1HodgeNumber degree
p1HodgeConjugationSymmetry degree00 = refl
p1HodgeConjugationSymmetry degree10 = refl
p1HodgeConjugationSymmetry degree01 = refl
p1HodgeConjugationSymmetry degree11 = refl

p1H00IsOne : p1HodgeNumber degree00 ≡ 1
p1H00IsOne = refl

p1H10IsZero : p1HodgeNumber degree10 ≡ 0
p1H10IsZero = refl

p1H01IsZero : p1HodgeNumber degree01 ≡ 0
p1H01IsZero = refl

p1H11IsOne : p1HodgeNumber degree11 ≡ 1
p1H11IsOne = refl

p1Betti0 : Nat
p1Betti0 = p1HodgeNumber degree00

p1Betti1 : Nat
p1Betti1 = p1HodgeNumber degree10 + p1HodgeNumber degree01

p1Betti2 : Nat
p1Betti2 = p1HodgeNumber degree11

p1BettiNumbers :
  p1Betti0 ≡ 1 × p1Betti1 ≡ 0 × p1Betti2 ≡ 1
p1BettiNumbers = refl , refl , refl

record ProjectiveLineGeometricIdentification : Setω where
  field
    projectiveLine : H.SmoothProjectiveComplexVariety
    complexDimensionIsOne : H.complexDimension projectiveLine ≡ 1
    comparison : H.SingularDeRhamComparison projectiveLine
    hodgeDecomposition : H.HodgeDecomposition projectiveLine comparison
    tableIdentifiesActualHodgeDimensions : Set
    hyperplanePointCycleGeneratesH11 : Set

open ProjectiveLineGeometricIdentification public

data ProjectiveLineProofStage : Set where
  finiteHodgeDiamondTable
  geometricCohomologyConstruction
  projectiveLineIdentification
  generalHodgeConjecture

finiteTableDoesNotProveGeneralHodge :
  finiteHodgeDiamondTable ≡ generalHodgeConjecture → ⊥
finiteTableDoesNotProveGeneralHodge ()
