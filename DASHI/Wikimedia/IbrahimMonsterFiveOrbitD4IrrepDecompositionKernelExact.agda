module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4IrrepDecompositionKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4PermutationCharacterKernelExact as Perm

------------------------------------------------------------------------
-- KERNEL-SOURCE D4 IRREDUCIBLE MULTIPLICITY ARITHMETIC
--
-- The explicit five-orbit D4 permutation action already computes the class
-- character
--
--   chi = (5,5,1,3,3)
--
-- on the ordered D4 conjugacy classes
--
--   e, r^2, {r,r^3}, axis reflections, diagonal reflections
--
-- with class sizes (1,1,2,2,2).
--
-- The standard D4 irreducible character rows are
--
--   A1 = ( 1, 1, 1, 1, 1)
--   A2 = ( 1, 1, 1,-1,-1)
--   B1 = ( 1, 1,-1, 1,-1)
--   B2 = ( 1, 1,-1,-1, 1)
--   E  = ( 2,-2, 0, 0, 0).
--
-- Instead of depending on an integer-division API, each multiplicity is
-- certified by splitting the weighted character inner-product numerator into
-- positive and negative Nat contributions and proving
--
--   positive = 8 * multiplicity + negative.
--
-- Thus the source-level decomposition is exactly
--
--   3 A1 + B1 + B2
--
-- with A2 = E = 0.  This remains distinct from an observed Agda kernel run
-- and from any Monster class-42d representation/action identification.
------------------------------------------------------------------------

chiIdentity : Nat
chiIdentity = Perm.identityFixedOrbitCount

chiHalfTurn : Nat
chiHalfTurn = Perm.halfTurnFixedOrbitCount

chiQuarterTurnClass : Nat
chiQuarterTurnClass = Perm.quarterTurnFixedOrbitCount

chiAxisReflectionClass : Nat
chiAxisReflectionClass = Perm.axisReflectionFixedOrbitCount

chiDiagonalReflectionClass : Nat
chiDiagonalReflectionClass = Perm.diagonalReflectionFixedOrbitCount

characterFiveFiveOneThreeThree :
  chiIdentity ≡ 5
characterFiveFiveOneThreeThree = refl

------------------------------------------------------------------------
-- Weighted signed-inner-product certificates.
------------------------------------------------------------------------

record MultiplicityCertificate : Set where
  constructor multiplicity-certificate
  field
    positiveWeightedSum : Nat
    negativeWeightedSum : Nat
    multiplicity : Nat
    weightedOrthogonalityEquation :
      positiveWeightedSum ≡ 8 * multiplicity + negativeWeightedSum
open MultiplicityCertificate public

a1Certificate : MultiplicityCertificate
a1Certificate = multiplicity-certificate
  (chiIdentity
   + chiHalfTurn
   + 2 * chiQuarterTurnClass
   + 2 * chiAxisReflectionClass
   + 2 * chiDiagonalReflectionClass)
  zero
  3
  refl

a2Certificate : MultiplicityCertificate
a2Certificate = multiplicity-certificate
  (chiIdentity
   + chiHalfTurn
   + 2 * chiQuarterTurnClass)
  (2 * chiAxisReflectionClass
   + 2 * chiDiagonalReflectionClass)
  0
  refl

b1Certificate : MultiplicityCertificate
b1Certificate = multiplicity-certificate
  (chiIdentity
   + chiHalfTurn
   + 2 * chiAxisReflectionClass)
  (2 * chiQuarterTurnClass
   + 2 * chiDiagonalReflectionClass)
  1
  refl

b2Certificate : MultiplicityCertificate
b2Certificate = multiplicity-certificate
  (chiIdentity
   + chiHalfTurn
   + 2 * chiDiagonalReflectionClass)
  (2 * chiQuarterTurnClass
   + 2 * chiAxisReflectionClass)
  1
  refl

eCertificate : MultiplicityCertificate
eCertificate = multiplicity-certificate
  (2 * chiIdentity)
  (2 * chiHalfTurn)
  0
  refl

a1Multiplicity : Nat
a1Multiplicity = multiplicity a1Certificate

a2Multiplicity : Nat
a2Multiplicity = multiplicity a2Certificate

b1Multiplicity : Nat
b1Multiplicity = multiplicity b1Certificate

b2Multiplicity : Nat
b2Multiplicity = multiplicity b2Certificate

eMultiplicity : Nat
eMultiplicity = multiplicity eCertificate

a1MultiplicityIsThree : a1Multiplicity ≡ 3
a1MultiplicityIsThree = refl

a2MultiplicityIsZero : a2Multiplicity ≡ 0
a2MultiplicityIsZero = refl

b1MultiplicityIsOne : b1Multiplicity ≡ 1
b1MultiplicityIsOne = refl

b2MultiplicityIsOne : b2Multiplicity ≡ 1
b2MultiplicityIsOne = refl

eMultiplicityIsZero : eMultiplicity ≡ 0
eMultiplicityIsZero = refl

------------------------------------------------------------------------
-- Dimension and raw-nine comparison.
------------------------------------------------------------------------

decompositionDimension : Nat
decompositionDimension =
  a1Multiplicity
  + a2Multiplicity
  + b1Multiplicity
  + b2Multiplicity
  + 2 * eMultiplicity

decompositionDimensionIsFive : decompositionDimension ≡ 5
decompositionDimensionIsFive = refl

rawNineEMultiplicity : Nat
rawNineEMultiplicity = 2

removedECopies : Nat
removedECopies = rawNineEMultiplicity + 0

removedECopiesIsTwo : removedECopies ≡ 2
removedECopiesIsTwo = refl

removedEDimension : Nat
removedEDimension = 2 * removedECopies

removedEDimensionIsFour : removedEDimension ≡ 4
removedEDimensionIsFour = refl

nineMinusRemovedDimensionWitness : 5 + removedEDimension ≡ 9
nineMinusRemovedDimensionWitness = refl

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data IrrepDecompositionCreatesMonster42dAction : Set where
data PythonMultiplicityCreatesKernelReceipt : Set where

data FiveOrbitIrrepContentCreatesOrbitIrrepBijection : Set where

irrepDecompositionDoesNotCreateMonster42dAction :
  IrrepDecompositionCreatesMonster42dAction → ⊥
irrepDecompositionDoesNotCreateMonster42dAction ()

pythonMultiplicityDoesNotCreateKernelReceipt :
  PythonMultiplicityCreatesKernelReceipt → ⊥
pythonMultiplicityDoesNotCreateKernelReceipt ()

fiveOrbitIrrepContentDoesNotCreateOrbitIrrepBijection :
  FiveOrbitIrrepContentCreatesOrbitIrrepBijection → ⊥
fiveOrbitIrrepContentDoesNotCreateOrbitIrrepBijection ()

------------------------------------------------------------------------
-- Status boundary.
------------------------------------------------------------------------

record FiveOrbitD4IrrepKernelBoundary : Set where
  constructor five-orbit-d4-irrep-kernel-boundary
  field
    permutationCharacterSourcePaid : Bool
    signedOrthogonalityArithmeticWritten : Bool
    agdaKernelIrrepDecompositionSourceWritten : Bool
    decompositionThreeA1B1B2Written : Bool
    a2MultiplicityZeroWritten : Bool
    eMultiplicityZeroWritten : Bool
    rawNineToQuotientRemovesTwoECopiesWritten : Bool
    agdaKernelIrrepDecompositionObserved : Bool
    orbitIrrepBijectionPaid : Bool
    irrepDecompositionCreatesMonster42dAction : Bool
    nextResidual : String
open FiveOrbitD4IrrepKernelBoundary public

currentFiveOrbitD4IrrepKernelBoundary : FiveOrbitD4IrrepKernelBoundary
currentFiveOrbitD4IrrepKernelBoundary =
  five-orbit-d4-irrep-kernel-boundary
    true true true true true true true
    false false false
    "Run the Agda validation to obtain an observed kernel receipt for the signed D4 orthogonality arithmetic. Once certified, use the exact five-orbit representation content 3*A1+B1+B2 (with A2=E=0), rather than the numeral 5, as the object compared against the Monster class-42d / N(3B) acquisition frontier. OEIS and Python remain discovery/cross-check surfaces and do not create the Monster action bridge."
