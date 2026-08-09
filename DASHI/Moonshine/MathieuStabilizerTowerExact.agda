module DASHI.Moonshine.MathieuStabilizerTowerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway, Robert T. Curtis, Simon P. Norton, Richard A. Parker,
-- and Robert A. Wilson,
-- "Atlas of Finite Groups", Oxford University Press, 1985.
-- No DOI assigned.
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- DASHI CONTRIBUTION
--
-- Formalize the exact order/index spine
--
--   8 --x9--> 72 --x10--> 720 --x11--> 7920 --x12--> 95040
--
-- as typed arithmetic stabilizer steps.  The arithmetic is internal and
-- exact.  The identification of these orders with successive point
-- stabilizers in the Mathieu actions is retained as source-bounded authority
-- rather than fabricated from cardinalities.  In particular, the order-eight
-- stabilizer is reported as quaternion Q8, not square-grid dihedral D4.
------------------------------------------------------------------------

open import Agda.Primitive using (Set)
open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Exact order spine.
------------------------------------------------------------------------

data MathieuLevel : Set where
  M8Level M9Level M10Level M11Level M12Level : MathieuLevel

levelOrder : MathieuLevel → Nat
levelOrder M8Level = 8
levelOrder M9Level = 72
levelOrder M10Level = 720
levelOrder M11Level = 7920
levelOrder M12Level = 95040

record StabilizerStep : Set where
  constructor stabilizerStep
  field
    lowerLevel : MathieuLevel
    upperLevel : MathieuLevel
    orbitSize : Nat
    orderLaw :
      levelOrder upperLevel
      ≡ orbitSize * levelOrder lowerLevel

open StabilizerStep public

step8To9 : StabilizerStep
step8To9 = stabilizerStep M8Level M9Level 9 refl

step9To10 : StabilizerStep
step9To10 = stabilizerStep M9Level M10Level 10 refl

step10To11 : StabilizerStep
step10To11 = stabilizerStep M10Level M11Level 11 refl

step11To12 : StabilizerStep
step11To12 = stabilizerStep M11Level M12Level 12 refl

m11OrderAsSuccessiveOrbits : levelOrder M11Level ≡ 8 * 9 * 10 * 11
m11OrderAsSuccessiveOrbits = refl

m12OrderAsSuccessiveOrbits :
  levelOrder M12Level ≡ 8 * 9 * 10 * 11 * 12
m12OrderAsSuccessiveOrbits = refl

m9FromM8 : 72 ≡ 9 * 8
m9FromM8 = refl

m10FromM9 : 720 ≡ 10 * 72
m10FromM9 = refl

m11FromM10 : 7920 ≡ 11 * 720
m11FromM10 = refl

m12FromM11 : 95040 ≡ 12 * 7920
m12FromM11 = refl

m11Factorization : 7920 ≡ 8 * 9 * 10 * 11
m11Factorization = refl

m12Factorization : 95040 ≡ 8 * 9 * 10 * 11 * 12
m12Factorization = refl

------------------------------------------------------------------------
-- Arithmetic witness only.
--
-- This record deliberately does not contain carriers, an action, a chosen
-- point, an inclusion, or finite-cardinality equivalences.  Those data are
-- required before promoting an order identity to a genuine orbit-stabilizer
-- construction.  Keeping the witness arithmetic-only prevents arbitrary
-- Sets plus unrelated Nat fields from masquerading as a group action.
------------------------------------------------------------------------

record OrbitStabilizerArithmeticWitness : Set where
  constructor orbitStabilizerArithmeticWitness
  field
    totalOrder : Nat
    stabilizerOrder : Nat
    orbitOrder : Nat
    orbitStabilizerOrderLaw : totalOrder ≡ orbitOrder * stabilizerOrder

open OrbitStabilizerArithmeticWitness public

record MathieuStepArithmeticWitness (step : StabilizerStep) : Set where
  constructor mathieuStepArithmeticWitness
  field
    witness : OrbitStabilizerArithmeticWitness
    totalMatchesUpper :
      totalOrder witness ≡ levelOrder (upperLevel step)
    stabilizerMatchesLower :
      stabilizerOrder witness ≡ levelOrder (lowerLevel step)
    orbitMatchesStep :
      orbitOrder witness ≡ orbitSize step

open MathieuStepArithmeticWitness public

stepArithmeticWitness :
  (step : StabilizerStep) →
  MathieuStepArithmeticWitness step
stepArithmeticWitness step =
  mathieuStepArithmeticWitness
    (orbitStabilizerArithmeticWitness
      (levelOrder (upperLevel step))
      (levelOrder (lowerLevel step))
      (orbitSize step)
      (orderLaw step))
    refl refl refl

step8To9ArithmeticWitness : MathieuStepArithmeticWitness step8To9
step8To9ArithmeticWitness = stepArithmeticWitness step8To9

step9To10ArithmeticWitness : MathieuStepArithmeticWitness step9To10
step9To10ArithmeticWitness = stepArithmeticWitness step9To10

step10To11ArithmeticWitness : MathieuStepArithmeticWitness step10To11
step10To11ArithmeticWitness = stepArithmeticWitness step10To11

step11To12ArithmeticWitness : MathieuStepArithmeticWitness step11To12
step11To12ArithmeticWitness = stepArithmeticWitness step11To12

------------------------------------------------------------------------
-- Source authority and anti-numerology boundaries.
------------------------------------------------------------------------

data OrderEightShape : Set where
  quaternionQ8 squareDihedralD4 unspecifiedOrderEight : OrderEightShape

atlasReportedM8Shape : OrderEightShape
atlasReportedM8Shape = quaternionQ8

atlasReportedM8IsQuaternion : atlasReportedM8Shape ≡ quaternionQ8
atlasReportedM8IsQuaternion = refl

atlasReportedM8IsNotD4 : atlasReportedM8Shape ≡ squareDihedralD4 → ⊥
atlasReportedM8IsNotD4 ()

q8Order : Nat
q8Order = 8

d4Order : Nat
d4Order = 8

equalOrderDoesNotChooseShape : q8Order ≡ d4Order
equalOrderDoesNotChooseShape = refl

record MathieuTowerBoundary : Set where
  constructor mathieuTowerBoundary
  field
    orderAndIndexArithmeticInternallyProved : Bool
    orderAndIndexArithmeticInternallyProvedIsTrue :
      orderAndIndexArithmeticInternallyProved ≡ true
    actualGroupActionsConstructedHere : Bool
    actualGroupActionsConstructedHereIsFalse :
      actualGroupActionsConstructedHere ≡ false
    arithmeticWitnessContainsActionLaws : Bool
    arithmeticWitnessContainsActionLawsIsFalse :
      arithmeticWitnessContainsActionLaws ≡ false
    atlasPointStabilizerDataIsExternalAuthority : Bool
    atlasPointStabilizerDataIsExternalAuthorityIsTrue :
      atlasPointStabilizerDataIsExternalAuthority ≡ true
    orderEightEqualityImpliesQ8IsD4 : Bool
    orderEightEqualityImpliesQ8IsD4IsFalse :
      orderEightEqualityImpliesQ8IsD4 ≡ false
    towerProvesModularJIdentification : Bool
    towerProvesModularJIdentificationIsFalse :
      towerProvesModularJIdentification ≡ false

canonicalMathieuTowerBoundary : MathieuTowerBoundary
canonicalMathieuTowerBoundary =
  mathieuTowerBoundary
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
