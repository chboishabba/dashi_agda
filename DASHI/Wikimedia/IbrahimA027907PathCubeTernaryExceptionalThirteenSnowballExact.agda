module DASHI.Wikimedia.IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Base369Ternary27PathCubeSpectralBandsExact as Bands
import DASHI.Wikimedia.IbrahimTernaryGeometricPartialSumRegularisationOEISSnowballExact as Geo
import DASHI.Wikimedia.IbrahimOneThreeSixOneNineTenBulkOEISSnowballExact as Bulk
import DASHI.Wikimedia.IbrahimExceptionalOEISHypothesisTestExact as Exceptional

------------------------------------------------------------------------
-- A027907 / P3^3 / TERNARY REPUNIT / EXCEPTIONAL-ARITHMETIC SEAM
--
-- The actual non-periodic 3x3x3 path-cube owner has spectral multiplicities
--
--   1,3,6,7,6,3,1.
--
-- This is exactly row n=3 of OEIS A027907, the trinomial coefficients of
-- (1+x+x^2)^n.  OEIS records two identities useful here:
--
--   rowSum(n) = 3^n,
--   sum_{k=0}^{n-1} T(n,2k) = (3^n-1)/2.
--
-- At n=3 this yields the exact repo-native seam
--
--   1+3+6+7+6+3+1 = 27,
--   1+6+6           = 13 = (27-1)/2 = 1+3+9 = 111_3.
--
-- The left flank also gives 1+3+6=10, hence the already-owned Monster bulk
--
--   196830 = (1+3+6) * 3^9.
--
-- Finally 13 refactors the existing exceptional arithmetic:
--
--   26=2*13, 27=1+2*13, 52=4*13, 53=1+4*13, 78=6*13.
--
-- These equalities are a typed arithmetic cross-pollination surface only.
-- They do NOT identify the path-cube representation, A003462 repunit carrier,
-- Albert/F4/E6 modules, or Monster residual/action carriers.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Literal path-cube row and its A027907 n=3 arithmetic.
------------------------------------------------------------------------

row0 : Nat
row0 = Bands.bandMultiplicity Bands.bandMinus3
row1 : Nat
row1 = Bands.bandMultiplicity Bands.bandMinus2
row2 : Nat
row2 = Bands.bandMultiplicity Bands.bandMinus1
row3 : Nat
row3 = Bands.bandMultiplicity Bands.bandZero
row4 : Nat
row4 = Bands.bandMultiplicity Bands.bandPlus1
row5 : Nat
row5 = Bands.bandMultiplicity Bands.bandPlus2
row6 : Nat
row6 = Bands.bandMultiplicity Bands.bandPlus3

rowIsA027907N3 :
  row0 ≡ 1 × row1 ≡ 3 × row2 ≡ 6 × row3 ≡ 7 ×
  row4 ≡ 6 × row5 ≡ 3 × row6 ≡ 1
rowIsA027907N3 = refl , refl , refl , refl , refl , refl , refl

rowSum : Nat
rowSum = row0 + row1 + row2 + row3 + row4 + row5 + row6

rowSumIs27 : rowSum ≡ 27
rowSumIs27 = Bands.spectralMultiplicityTotalIs27

leftFlank : Nat
leftFlank = row0 + row1 + row2

leftFlankIsTen : leftFlank ≡ 10
leftFlankIsTen = refl

leftFlankMatchesOuterTen : leftFlank ≡ 1 + 3 + 6
leftFlankMatchesOuterTen = refl

------------------------------------------------------------------------
-- 2. OEIS A027907 even-position sub-sum at n=3 = A003462(3).
------------------------------------------------------------------------

evenPrefix : Nat
evenPrefix = row0 + row2 + row4

evenPrefixIs13 : evenPrefix ≡ 13
evenPrefixIs13 = refl

evenPrefixMatchesTernaryPartial3 : evenPrefix ≡ Geo.partialSum3 3
evenPrefixMatchesTernaryPartial3 = refl

thirteenIsTernaryRepunit : Geo.partialSum3 3 ≡ 1 + 3 + 9
thirteenIsTernaryRepunit = refl

oddInterior : Nat
oddInterior = row1 + row3 + row5

oddInteriorIs13 : oddInterior ≡ 13
oddInteriorIs13 = refl

rowAsThirteenThirteenOne : rowSum ≡ 13 + 13 + 1
rowAsThirteenThirteenOne = refl

------------------------------------------------------------------------
-- 3. Existing Monster 196830 outer-ten carrier becomes path-row-addressable.
------------------------------------------------------------------------

bulkAsPathLeftFlankTimesThreePowerNine : leftFlank * 19683 ≡ 196830
bulkAsPathLeftFlankTimesThreePowerNine = refl

bulkStillOwnedByExistingTenCarrier :
  (1 + 3 + 6) * 19683 ≡ Bulk.bulk
bulkStillOwnedByExistingTenCarrier = refl

------------------------------------------------------------------------
-- 4. Thirteen-atom refactor of the existing exceptional arithmetic.
------------------------------------------------------------------------

twentySixAsTwoThirteen : 26 ≡ 2 * 13
twentySixAsTwoThirteen = refl

twentySevenAsOnePlusTwoThirteen : 27 ≡ 1 + 2 * 13
twentySevenAsOnePlusTwoThirteen = refl

fiftyTwoAsFourThirteen : 52 ≡ 4 * 13
fiftyTwoAsFourThirteen = refl

fiftyThreeAsOnePlusFourThirteen : 53 ≡ 1 + 4 * 13
fiftyThreeAsOnePlusFourThirteen = refl

seventyEightAsSixThirteen : 78 ≡ 6 * 13
seventyEightAsSixThirteen = refl

exceptional52StillMatchesExistingOwner : 52 ≡ 26 + 26
exceptional52StillMatchesExistingOwner = Exceptional.f4AdjointAsTwo26

exceptional53StillMatchesExistingOwner : 53 ≡ 1 + (26 + 26)
exceptional53StillMatchesExistingOwner = Exceptional.reduced53AsOnePlusTwo26

exceptional78StillMatchesExistingOwner : 78 ≡ 52 + 26
exceptional78StillMatchesExistingOwner = Exceptional.e6AdjointAsF4Plus26

------------------------------------------------------------------------
-- 5. External coordinate and promotion strength.
------------------------------------------------------------------------

record A027907ThirteenCoordinates : Set where
  constructor a027907-thirteen-coordinates
  field
    trinomialTriangleOEIS : String
    powersOfThreeOEIS : String
    ternaryPartialSumOEIS : String
    tenTimesPowerThreeOEIS : String
    rowN3Exact : Bool
    rowSum27Exact : Bool
    evenPrefix13Exact : Bool
    leftFlank10Exact : Bool
    exceptionalRefactorArithmeticExact : Bool
    sameActionBridgePaid : Bool
open A027907ThirteenCoordinates public

canonicalA027907ThirteenCoordinates : A027907ThirteenCoordinates
canonicalA027907ThirteenCoordinates = a027907-thirteen-coordinates
  "A027907" "A000244" "A003462" "A005052"
  true true true true true false

------------------------------------------------------------------------
-- 6. Bidi / WrongType firewalls.
------------------------------------------------------------------------

data SameThirteenIdentifiesCarrier : Set where
data PathCube27CreatesE6Minuscule : Set where
data TrinomialRowCreatesAlbertAction : Set where
data ThirteenRefactorCreatesF4E6Intertwiner : Set where
data LeftFlankTenCreatesMonsterAction : Set where

equalThirteenDoesNotIdentifyCarrier : SameThirteenIdentifiesCarrier → ⊥
equalThirteenDoesNotIdentifyCarrier ()

pathCubeDimensionDoesNotCreateE6Minuscule : PathCube27CreatesE6Minuscule → ⊥
pathCubeDimensionDoesNotCreateE6Minuscule ()

trinomialRowDoesNotCreateAlbertAction : TrinomialRowCreatesAlbertAction → ⊥
trinomialRowDoesNotCreateAlbertAction ()

thirteenRefactorDoesNotCreateExceptionalIntertwiner :
  ThirteenRefactorCreatesF4E6Intertwiner → ⊥
thirteenRefactorDoesNotCreateExceptionalIntertwiner ()

leftFlankDoesNotCreateMonsterAction : LeftFlankTenCreatesMonsterAction → ⊥
leftFlankDoesNotCreateMonsterAction ()

record A027907PathCubeThirteenFrontier : Set where
  constructor a027907-path-cube-thirteen-frontier
  field
    literalPathCubeMultiplicityRowPaid : Bool
    a027907N3RolePaid : Bool
    rowSumThreeCubedPaid : Bool
    canonicalEvenPrefixThirteenPaid : Bool
    a003462ThirteenSameIntegerPaid : Bool
    leftFlankOneThreeSixTenPaid : Bool
    bulk196830RefactorPaid : Bool
    exceptionalThirteenAtomArithmeticPaid : Bool
    pathCubeToExceptionalSameActionPaid : Bool
    nextResidual : String
open A027907PathCubeThirteenFrontier public

currentA027907PathCubeThirteenFrontier : A027907PathCubeThirteenFrontier
currentA027907PathCubeThirteenFrontier = a027907-path-cube-thirteen-frontier
  true true true true true true true true false
  "test the n=3 trinomial-row structure as a consumer-preserving bridge, not a numeral bridge: first compare the literal P3^3 tensor-product construction with the ternary digit/product carrier that generates A027907; separately test whether any existing Albert/E6 27-dimensional action factors through that same product carrier. Until an intertwiner survives, retain 13 only as a shared arithmetic atom and A027907 as an exact combinatorial explanation of the path-cube multiplicities."