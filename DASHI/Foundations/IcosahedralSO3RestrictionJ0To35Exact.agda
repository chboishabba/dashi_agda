module DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- DASHI CONTRIBUTION
--
-- Restrict the SO(3) angular-momentum scan j=0..35 to the rotational
-- icosahedral group I ~= A5.  The five finite irreps have dimensions
-- 1,3,3,4,5.  The two order-five classes are kept distinct and their character
-- values are represented exactly in Z[phi] by pairs a+b*phi.
--
-- The scan includes Ogg and non-Ogg dimensions uniformly.  It exposes the
-- exact control law Res_I V_(j+30) = Res_I V_j + Reg_I on j=0..5, including
-- the Ogg dimension 7 at j=3 and non-Ogg dimension 67 at j=33.  Therefore a
-- selector that only sees the A5 branching modulo regular representation
-- cannot characterize the Ogg set.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_; -[1+_])

import DASHI.Foundations.FiniteRepresentationRestrictionCore as Core
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin

record PhiInt : Set where
  constructor phi-int
  field
    rationalPart goldenPart : ℤ

open PhiInt public

phiZero phiOne phi goldenConjugate phiMinusOne : PhiInt
phiZero = phi-int (+ 0) (+ 0)
phiOne = phi-int (+ 1) (+ 0)
phi = phi-int (+ 0) (+ 1)
goldenConjugate = phi-int (+ 1) (-[1+ 0 ])
phiMinusOne = phi-int (-[1+ 0 ]) (+ 1)

data IcosahedralIrrep : Set where
  I1 I3 I3Prime I4 I5 : IcosahedralIrrep

icosahedralIrrepDimension : IcosahedralIrrep → Nat
icosahedralIrrepDimension I1 = 1
icosahedralIrrepDimension I3 = 3
icosahedralIrrepDimension I3Prime = 3
icosahedralIrrepDimension I4 = 4
icosahedralIrrepDimension I5 = 5

allIcosahedralIrreps : List IcosahedralIrrep
allIcosahedralIrreps = I1 ∷ I3 ∷ I3Prime ∷ I4 ∷ I5 ∷ []

icosahedralFamily : Core.FiniteIrrepFamily
icosahedralFamily =
  Core.finite-irrep-family
    IcosahedralIrrep
    allIcosahedralIrreps
    icosahedralIrrepDimension
    "rotational icosahedral group I ~= A5; irreps 1,3,3',4,5"

data IcosahedralClass : Set where
  identityClass halfTurnClass thirdTurnClass fifthTurnClass fifthTurnSquaredClass : IcosahedralClass

irrepCharacter : IcosahedralIrrep → IcosahedralClass → PhiInt
irrepCharacter I1 identityClass = phi-int (+ 1) (+ 0)
irrepCharacter I1 halfTurnClass = phi-int (+ 1) (+ 0)
irrepCharacter I1 thirdTurnClass = phi-int (+ 1) (+ 0)
irrepCharacter I1 fifthTurnClass = phi-int (+ 1) (+ 0)
irrepCharacter I1 fifthTurnSquaredClass = phi-int (+ 1) (+ 0)
irrepCharacter I3 identityClass = phi-int (+ 3) (+ 0)
irrepCharacter I3 halfTurnClass = phi-int (-[1+ 0 ]) (+ 0)
irrepCharacter I3 thirdTurnClass = phi-int (+ 0) (+ 0)
irrepCharacter I3 fifthTurnClass = phi
irrepCharacter I3 fifthTurnSquaredClass = goldenConjugate
irrepCharacter I3Prime identityClass = phi-int (+ 3) (+ 0)
irrepCharacter I3Prime halfTurnClass = phi-int (-[1+ 0 ]) (+ 0)
irrepCharacter I3Prime thirdTurnClass = phi-int (+ 0) (+ 0)
irrepCharacter I3Prime fifthTurnClass = goldenConjugate
irrepCharacter I3Prime fifthTurnSquaredClass = phi
irrepCharacter I4 identityClass = phi-int (+ 4) (+ 0)
irrepCharacter I4 halfTurnClass = phi-int (+ 0) (+ 0)
irrepCharacter I4 thirdTurnClass = phi-int (+ 1) (+ 0)
irrepCharacter I4 fifthTurnClass = phi-int (-[1+ 0 ]) (+ 0)
irrepCharacter I4 fifthTurnSquaredClass = phi-int (-[1+ 0 ]) (+ 0)
irrepCharacter I5 identityClass = phi-int (+ 5) (+ 0)
irrepCharacter I5 halfTurnClass = phi-int (+ 1) (+ 0)
irrepCharacter I5 thirdTurnClass = phi-int (-[1+ 0 ]) (+ 0)
irrepCharacter I5 fifthTurnClass = phiZero
irrepCharacter I5 fifthTurnSquaredClass = phiZero

record IcosahedralSpectrum : Set where
  constructor ico-spectrum
  field
    multiplicityI1 multiplicityI3 multiplicityI3Prime multiplicityI4 multiplicityI5 : Nat

open IcosahedralSpectrum public

multiplicityOf : IcosahedralSpectrum → IcosahedralIrrep → Nat
multiplicityOf spectrum I1 = multiplicityI1 spectrum
multiplicityOf spectrum I3 = multiplicityI3 spectrum
multiplicityOf spectrum I3Prime = multiplicityI3Prime spectrum
multiplicityOf spectrum I4 = multiplicityI4 spectrum
multiplicityOf spectrum I5 = multiplicityI5 spectrum

branchingDimension : IcosahedralSpectrum → Nat
branchingDimension spectrum =
  Core.sumWeighted allIcosahedralIrreps icosahedralIrrepDimension (multiplicityOf spectrum)

branchingSpectrum : Spin.AngularMomentum0To35 → IcosahedralSpectrum
branchingSpectrum Spin.j0 = ico-spectrum 1 0 0 0 0
branchingSpectrum Spin.j1 = ico-spectrum 0 1 0 0 0
branchingSpectrum Spin.j2 = ico-spectrum 0 0 0 0 1
branchingSpectrum Spin.j3 = ico-spectrum 0 0 1 1 0
branchingSpectrum Spin.j4 = ico-spectrum 0 0 0 1 1
branchingSpectrum Spin.j5 = ico-spectrum 0 1 1 0 1
branchingSpectrum Spin.j6 = ico-spectrum 1 1 0 1 1
branchingSpectrum Spin.j7 = ico-spectrum 0 1 1 1 1
branchingSpectrum Spin.j8 = ico-spectrum 0 0 1 1 2
branchingSpectrum Spin.j9 = ico-spectrum 0 1 1 2 1
branchingSpectrum Spin.j10 = ico-spectrum 1 1 1 1 2
branchingSpectrum Spin.j11 = ico-spectrum 0 2 1 1 2
branchingSpectrum Spin.j12 = ico-spectrum 1 1 1 2 2
branchingSpectrum Spin.j13 = ico-spectrum 0 1 2 2 2
branchingSpectrum Spin.j14 = ico-spectrum 0 1 1 2 3
branchingSpectrum Spin.j15 = ico-spectrum 1 2 2 2 2
branchingSpectrum Spin.j16 = ico-spectrum 1 2 1 2 3
branchingSpectrum Spin.j17 = ico-spectrum 0 2 2 2 3
branchingSpectrum Spin.j18 = ico-spectrum 1 1 2 3 3
branchingSpectrum Spin.j19 = ico-spectrum 0 2 2 3 3
branchingSpectrum Spin.j20 = ico-spectrum 1 2 2 2 4
branchingSpectrum Spin.j21 = ico-spectrum 1 3 2 3 3
branchingSpectrum Spin.j22 = ico-spectrum 1 2 2 3 4
branchingSpectrum Spin.j23 = ico-spectrum 0 2 3 3 4
branchingSpectrum Spin.j24 = ico-spectrum 1 2 2 4 4
branchingSpectrum Spin.j25 = ico-spectrum 1 3 3 3 4
branchingSpectrum Spin.j26 = ico-spectrum 1 3 2 3 5
branchingSpectrum Spin.j27 = ico-spectrum 1 3 3 4 4
branchingSpectrum Spin.j28 = ico-spectrum 1 2 3 4 5
branchingSpectrum Spin.j29 = ico-spectrum 0 3 3 4 5
branchingSpectrum Spin.j30 = ico-spectrum 2 3 3 4 5
branchingSpectrum Spin.j31 = ico-spectrum 1 4 3 4 5
branchingSpectrum Spin.j32 = ico-spectrum 1 3 3 4 6
branchingSpectrum Spin.j33 = ico-spectrum 1 3 4 5 5
branchingSpectrum Spin.j34 = ico-spectrum 1 3 3 5 6
branchingSpectrum Spin.j35 = ico-spectrum 1 4 4 4 6

branchingDimensionExact :
  (j : Spin.AngularMomentum0To35) →
  branchingDimension (branchingSpectrum j) ≡ Spin.jDimension j
branchingDimensionExact Spin.j0 = refl
branchingDimensionExact Spin.j1 = refl
branchingDimensionExact Spin.j2 = refl
branchingDimensionExact Spin.j3 = refl
branchingDimensionExact Spin.j4 = refl
branchingDimensionExact Spin.j5 = refl
branchingDimensionExact Spin.j6 = refl
branchingDimensionExact Spin.j7 = refl
branchingDimensionExact Spin.j8 = refl
branchingDimensionExact Spin.j9 = refl
branchingDimensionExact Spin.j10 = refl
branchingDimensionExact Spin.j11 = refl
branchingDimensionExact Spin.j12 = refl
branchingDimensionExact Spin.j13 = refl
branchingDimensionExact Spin.j14 = refl
branchingDimensionExact Spin.j15 = refl
branchingDimensionExact Spin.j16 = refl
branchingDimensionExact Spin.j17 = refl
branchingDimensionExact Spin.j18 = refl
branchingDimensionExact Spin.j19 = refl
branchingDimensionExact Spin.j20 = refl
branchingDimensionExact Spin.j21 = refl
branchingDimensionExact Spin.j22 = refl
branchingDimensionExact Spin.j23 = refl
branchingDimensionExact Spin.j24 = refl
branchingDimensionExact Spin.j25 = refl
branchingDimensionExact Spin.j26 = refl
branchingDimensionExact Spin.j27 = refl
branchingDimensionExact Spin.j28 = refl
branchingDimensionExact Spin.j29 = refl
branchingDimensionExact Spin.j30 = refl
branchingDimensionExact Spin.j31 = refl
branchingDimensionExact Spin.j32 = refl
branchingDimensionExact Spin.j33 = refl
branchingDimensionExact Spin.j34 = refl
branchingDimensionExact Spin.j35 = refl

icosahedralBranching :
  (j : Spin.AngularMomentum0To35) →
  Core.BranchingSpectrum (Spin.continuousSO3Irrep j) icosahedralFamily
icosahedralBranching j =
  Core.branching-spectrum
    (multiplicityOf (branchingSpectrum j))
    (branchingDimensionExact j)
    "exact rotational-icosahedral restriction on the j=0..35 control scan"

regularSpectrum : IcosahedralSpectrum
regularSpectrum = ico-spectrum 1 3 3 4 5

addSpectrum : IcosahedralSpectrum → IcosahedralSpectrum → IcosahedralSpectrum
addSpectrum left right =
  ico-spectrum
    (multiplicityI1 left + multiplicityI1 right)
    (multiplicityI3 left + multiplicityI3 right)
    (multiplicityI3Prime left + multiplicityI3Prime right)
    (multiplicityI4 left + multiplicityI4 right)
    (multiplicityI5 left + multiplicityI5 right)

data LowJ0To5 : Set where
  lowJ0 lowJ1 lowJ2 lowJ3 lowJ4 lowJ5 : LowJ0To5

embedLowJ : LowJ0To5 → Spin.AngularMomentum0To35
embedLowJ lowJ0 = Spin.j0
embedLowJ lowJ1 = Spin.j1
embedLowJ lowJ2 = Spin.j2
embedLowJ lowJ3 = Spin.j3
embedLowJ lowJ4 = Spin.j4
embedLowJ lowJ5 = Spin.j5

shiftLowJBy30 : LowJ0To5 → Spin.AngularMomentum0To35
shiftLowJBy30 lowJ0 = Spin.j30
shiftLowJBy30 lowJ1 = Spin.j31
shiftLowJBy30 lowJ2 = Spin.j32
shiftLowJBy30 lowJ3 = Spin.j33
shiftLowJBy30 lowJ4 = Spin.j34
shiftLowJBy30 lowJ5 = Spin.j35

regularShiftBy30Exact :
  (j : LowJ0To5) →
  branchingSpectrum (shiftLowJBy30 j)
  ≡ addSpectrum regularSpectrum (branchingSpectrum (embedLowJ j))
regularShiftBy30Exact lowJ0 = refl
regularShiftBy30Exact lowJ1 = refl
regularShiftBy30Exact lowJ2 = refl
regularShiftBy30Exact lowJ3 = refl
regularShiftBy30Exact lowJ4 = refl
regularShiftBy30Exact lowJ5 = refl

j3ToJ33IsOneRegularShift :
  branchingSpectrum Spin.j33
  ≡ addSpectrum regularSpectrum (branchingSpectrum Spin.j3)
j3ToJ33IsOneRegularShift = refl

j4NineBranching : branchingSpectrum Spin.j4 ≡ ico-spectrum 0 0 0 1 1
j4NineBranching = refl

record IcosahedralRestrictionBoundary : Set where
  field
    exactBranchingJ0To35Constructed : Bool
    exactBranchingJ0To35ConstructedIsTrue : exactBranchingJ0To35Constructed ≡ true
    orderFiveClassesKeptDistinct : Bool
    orderFiveClassesKeptDistinctIsTrue : orderFiveClassesKeptDistinct ≡ true
    regularQuotientPeriodThirtyProvedOnScan : Bool
    regularQuotientPeriodThirtyProvedOnScanIsTrue : regularQuotientPeriodThirtyProvedOnScan ≡ true
    fixedA5QuotientClaimedToCharacterizeOgg : Bool
    fixedA5QuotientClaimedToCharacterizeOggIsFalse : fixedA5QuotientClaimedToCharacterizeOgg ≡ false

canonicalIcosahedralRestrictionBoundary : IcosahedralRestrictionBoundary
canonicalIcosahedralRestrictionBoundary =
  record
    { exactBranchingJ0To35Constructed = true
    ; exactBranchingJ0To35ConstructedIsTrue = refl
    ; orderFiveClassesKeptDistinct = true
    ; orderFiveClassesKeptDistinctIsTrue = refl
    ; regularQuotientPeriodThirtyProvedOnScan = true
    ; regularQuotientPeriodThirtyProvedOnScanIsTrue = refl
    ; fixedA5QuotientClaimedToCharacterizeOgg = false
    ; fixedA5QuotientClaimedToCharacterizeOggIsFalse = refl
    }
