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
-- as typed stabilizer steps.  The arithmetic is internal and exact.  The
-- identification of these orders with the successive point stabilizers in
-- the Mathieu actions is retained as source-bounded authority rather than
-- fabricated from cardinalities.  In particular, the order-eight stabilizer
-- is reported as quaternion Q8, not the square-grid dihedral group D4.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
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
-- Generic finite orbit--stabilizer carrier.
------------------------------------------------------------------------

record PointedOrbitFibration : Set₁ where
  field
    TotalTransformation : Set
    Point : Set
    StabilizerFibre : Set

    chosenPoint : Point
    transportPoint : TotalTransformation → Point
    includeStabilizer : StabilizerFibre → TotalTransformation

    totalOrder : Nat
    fibreOrder : Nat
    orbitOrder : Nat
    orbitStabilizerOrderLaw : totalOrder ≡ orbitOrder * fibreOrder

open PointedOrbitFibration public

record MathieuStepRealization (step : StabilizerStep) : Set₁ where
  field
    fibration : PointedOrbitFibration
    totalMatchesUpper :
      totalOrder fibration ≡ levelOrder (upperLevel step)
    fibreMatchesLower :
      fibreOrder fibration ≡ levelOrder (lowerLevel step)
    orbitMatchesStep :
      orbitOrder fibration ≡ orbitSize step

open MathieuStepRealization public

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
  mathieuTowerBoundary true refl false refl true refl false refl false refl
