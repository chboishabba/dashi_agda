module DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- DASHI CONTRIBUTION
--
-- Construct the standard generator-level Schrodinger/Weyl model on
--
--   X = F_3^6.
--
-- Translation generators T_a increment one coordinate.  Modulation
-- generators M_b read one dual coordinate and contribute the phase exponent
-- <b,x>.  The exact generator relation
--
--   M_b T_a = zeta^{<b,a>} T_a M_b
--
-- is represented without importing complex analysis by the exponent identity
--
--   <b,x+a> = <b,a> + <b,x> in F_3.
--
-- All 36 standard generator pairs reduce definitionally.  This proves the
-- concrete generator algebra used by the executable 729-state model.  It is
-- not yet the finite Stone--von Neumann uniqueness theorem or an embedding in
-- the actual Monster module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

------------------------------------------------------------------------
-- F_3 exponent arithmetic, with neg=2, zer=0, pos=1.
------------------------------------------------------------------------

infixl 6 _+3_

_+3_ : Trit → Trit → Trit
zer +3 b = b
pos +3 zer = pos
pos +3 pos = neg
pos +3 neg = zer
neg +3 zer = neg
neg +3 pos = zer
neg +3 neg = pos

negate3 : Trit → Trit
negate3 zer = zer
negate3 pos = neg
negate3 neg = pos

threePhaseCycle : pos +3 (pos +3 pos) ≡ zer
threePhaseCycle = refl

posThenNeg : (value : Trit) → negate3 pos +3 (pos +3 value) ≡ value
posThenNeg neg = refl
posThenNeg zer = refl
posThenNeg pos = refl

negThenPos : (value : Trit) → pos +3 (negate3 pos +3 value) ≡ value
negThenPos neg = refl
negThenPos zer = refl
negThenPos pos = refl

------------------------------------------------------------------------
-- The six-dimensional Lagrangian coordinate X=F_3^6.
------------------------------------------------------------------------

record X6 : Set where
  constructor x6
  field
    x0 : Trit
    x1 : Trit
    x2 : Trit
    x3 : Trit
    x4 : Trit
    x5 : Trit

open X6 public

data Axis6 : Set where
  axis0 : Axis6
  axis1 : Axis6
  axis2 : Axis6
  axis3 : Axis6
  axis4 : Axis6
  axis5 : Axis6

coordinate : Axis6 → X6 → Trit
coordinate axis0 x = x0 x
coordinate axis1 x = x1 x
coordinate axis2 x = x2 x
coordinate axis3 x = x3 x
coordinate axis4 x = x4 x
coordinate axis5 x = x5 x

increment : Trit → Trit
increment value = pos +3 value

decrement : Trit → Trit
decrement value = neg +3 value

translate : Axis6 → X6 → X6
translate axis0 x = x6 (increment (x0 x)) (x1 x) (x2 x) (x3 x) (x4 x) (x5 x)
translate axis1 x = x6 (x0 x) (increment (x1 x)) (x2 x) (x3 x) (x4 x) (x5 x)
translate axis2 x = x6 (x0 x) (x1 x) (increment (x2 x)) (x3 x) (x4 x) (x5 x)
translate axis3 x = x6 (x0 x) (x1 x) (x2 x) (increment (x3 x)) (x4 x) (x5 x)
translate axis4 x = x6 (x0 x) (x1 x) (x2 x) (x3 x) (increment (x4 x)) (x5 x)
translate axis5 x = x6 (x0 x) (x1 x) (x2 x) (x3 x) (x4 x) (increment (x5 x))

translateInverse : Axis6 → X6 → X6
translateInverse axis0 x = x6 (decrement (x0 x)) (x1 x) (x2 x) (x3 x) (x4 x) (x5 x)
translateInverse axis1 x = x6 (x0 x) (decrement (x1 x)) (x2 x) (x3 x) (x4 x) (x5 x)
translateInverse axis2 x = x6 (x0 x) (x1 x) (decrement (x2 x)) (x3 x) (x4 x) (x5 x)
translateInverse axis3 x = x6 (x0 x) (x1 x) (x2 x) (decrement (x3 x)) (x4 x) (x5 x)
translateInverse axis4 x = x6 (x0 x) (x1 x) (x2 x) (x3 x) (decrement (x4 x)) (x5 x)
translateInverse axis5 x = x6 (x0 x) (x1 x) (x2 x) (x3 x) (x4 x) (decrement (x5 x))

------------------------------------------------------------------------
-- Standard dual generators and the generator-level pairing.
------------------------------------------------------------------------

kronecker : Axis6 → Axis6 → Trit
kronecker axis0 axis0 = pos
kronecker axis0 axis1 = zer
kronecker axis0 axis2 = zer
kronecker axis0 axis3 = zer
kronecker axis0 axis4 = zer
kronecker axis0 axis5 = zer
kronecker axis1 axis0 = zer
kronecker axis1 axis1 = pos
kronecker axis1 axis2 = zer
kronecker axis1 axis3 = zer
kronecker axis1 axis4 = zer
kronecker axis1 axis5 = zer
kronecker axis2 axis0 = zer
kronecker axis2 axis1 = zer
kronecker axis2 axis2 = pos
kronecker axis2 axis3 = zer
kronecker axis2 axis4 = zer
kronecker axis2 axis5 = zer
kronecker axis3 axis0 = zer
kronecker axis3 axis1 = zer
kronecker axis3 axis2 = zer
kronecker axis3 axis3 = pos
kronecker axis3 axis4 = zer
kronecker axis3 axis5 = zer
kronecker axis4 axis0 = zer
kronecker axis4 axis1 = zer
kronecker axis4 axis2 = zer
kronecker axis4 axis3 = zer
kronecker axis4 axis4 = pos
kronecker axis4 axis5 = zer
kronecker axis5 axis0 = zer
kronecker axis5 axis1 = zer
kronecker axis5 axis2 = zer
kronecker axis5 axis3 = zer
kronecker axis5 axis4 = zer
kronecker axis5 axis5 = pos

modulationExponent : Axis6 → X6 → Trit
modulationExponent = coordinate

------------------------------------------------------------------------
-- Generator Weyl relation in phase-exponent form.
------------------------------------------------------------------------

generatorWeylExponent :
  (dual translationAxis : Axis6) →
  (state : X6) →
  modulationExponent dual (translate translationAxis state)
  ≡ kronecker dual translationAxis +3 modulationExponent dual state
generatorWeylExponent axis0 axis0 state = refl
generatorWeylExponent axis0 axis1 state = refl
generatorWeylExponent axis0 axis2 state = refl
generatorWeylExponent axis0 axis3 state = refl
generatorWeylExponent axis0 axis4 state = refl
generatorWeylExponent axis0 axis5 state = refl
generatorWeylExponent axis1 axis0 state = refl
generatorWeylExponent axis1 axis1 state = refl
generatorWeylExponent axis1 axis2 state = refl
generatorWeylExponent axis1 axis3 state = refl
generatorWeylExponent axis1 axis4 state = refl
generatorWeylExponent axis1 axis5 state = refl
generatorWeylExponent axis2 axis0 state = refl
generatorWeylExponent axis2 axis1 state = refl
generatorWeylExponent axis2 axis2 state = refl
generatorWeylExponent axis2 axis3 state = refl
generatorWeylExponent axis2 axis4 state = refl
generatorWeylExponent axis2 axis5 state = refl
generatorWeylExponent axis3 axis0 state = refl
generatorWeylExponent axis3 axis1 state = refl
generatorWeylExponent axis3 axis2 state = refl
generatorWeylExponent axis3 axis3 state = refl
generatorWeylExponent axis3 axis4 state = refl
generatorWeylExponent axis3 axis5 state = refl
generatorWeylExponent axis4 axis0 state = refl
generatorWeylExponent axis4 axis1 state = refl
generatorWeylExponent axis4 axis2 state = refl
generatorWeylExponent axis4 axis3 state = refl
generatorWeylExponent axis4 axis4 state = refl
generatorWeylExponent axis4 axis5 state = refl
generatorWeylExponent axis5 axis0 state = refl
generatorWeylExponent axis5 axis1 state = refl
generatorWeylExponent axis5 axis2 state = refl
generatorWeylExponent axis5 axis3 state = refl
generatorWeylExponent axis5 axis4 state = refl
generatorWeylExponent axis5 axis5 state = refl

------------------------------------------------------------------------
-- Basic generator counts and epistemic boundary.
------------------------------------------------------------------------

translationGeneratorCount : Nat
translationGeneratorCount = 6

modulationGeneratorCount : Nat
modulationGeneratorCount = 6

standardGeneratorPairCount : Nat
standardGeneratorPairCount = translationGeneratorCount * modulationGeneratorCount

standardGeneratorPairCountIsThirtySix : standardGeneratorPairCount ≡ 36
standardGeneratorPairCountIsThirtySix = refl

schrodingerBasisDimension : Nat
schrodingerBasisDimension = 729

record FiniteHeisenbergBoundary : Set where
  constructor finiteHeisenbergBoundary
  field
    generatorWeylRelationsProved : Bool
    generatorWeylRelationsProvedIsTrue :
      generatorWeylRelationsProved ≡ true
    finiteStoneVonNeumannUniquenessProved : Bool
    finiteStoneVonNeumannUniquenessProvedIsFalse :
      finiteStoneVonNeumannUniquenessProved ≡ false
    actualMN3BGeneratorMatricesImported : Bool
    actualMN3BGeneratorMatricesImportedIsFalse :
      actualMN3BGeneratorMatricesImported ≡ false

canonicalFiniteHeisenbergBoundary : FiniteHeisenbergBoundary
canonicalFiniteHeisenbergBoundary =
  finiteHeisenbergBoundary true refl false refl false refl
