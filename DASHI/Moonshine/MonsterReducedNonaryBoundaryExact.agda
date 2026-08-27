module DASHI.Moonshine.MonsterReducedNonaryBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- DASHI CONTRIBUTION
--
-- Refine the existing 54 -> 53 reduction by localising the removed invariant
-- line inside one distinguished nine-sector:
--
--   54 = 5*9 + 9,
--   53 = 5*9 + (9-1) = 45 + 8.
--
-- This is theorem-level finite arithmetic and agrees with the existing
-- six-by-nine reduced-mode construction.  The later 54/56/64 ledger is also
-- recorded exactly, but no semantic claim that the numerical gap 2 literally
-- counts "failed gluings" is promoted without a concrete gluing complex.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat using (_∸_)

import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic

fiveCompleteNonarySectors : Nat
fiveCompleteNonarySectors = 5 * 9

distinguishedNonarySector : Nat
distinguishedNonarySector = 9

reducedDistinguishedNonarySector : Nat
reducedDistinguishedNonarySector = distinguishedNonarySector ∸ 1

fullSixByNine : Nat
fullSixByNine = fiveCompleteNonarySectors + distinguishedNonarySector

reducedSixByNine : Nat
reducedSixByNine =
  fiveCompleteNonarySectors + reducedDistinguishedNonarySector

fiveCompleteNonarySectorsIsFortyFive :
  fiveCompleteNonarySectors ≡ 45
fiveCompleteNonarySectorsIsFortyFive = refl

fullSixByNineIsFiftyFour : fullSixByNine ≡ 54
fullSixByNineIsFiftyFour = refl

reducedDistinguishedNonarySectorIsEight :
  reducedDistinguishedNonarySector ≡ 8
reducedDistinguishedNonarySectorIsEight = refl

reducedSixByNineIsFiftyThree : reducedSixByNine ≡ 53
reducedSixByNineIsFiftyThree = refl

fiftyThreeIsFortyFivePlusEight : 45 + 8 ≡ 53
fiftyThreeIsFortyFivePlusEight = refl

fiftyFourIsFortyFivePlusNine : 45 + 9 ≡ 54
fiftyFourIsFortyFivePlusNine = refl

localisedReductionAgreesWithExistingReducedDimension :
  reducedSixByNine ≡ Reduced.reducedDimension
localisedReductionAgreesWithExistingReducedDimension = refl

localisedFullAgreesWithExistingFullDimension :
  fullSixByNine ≡ Reduced.fullSixByNineDimension
localisedFullAgreesWithExistingFullDimension = refl

------------------------------------------------------------------------
-- Internal 5 x 3 x 3 reading: forty-five is five full nonary sectors, or
-- equivalently five modes times two ternary coordinates.  This is cardinal
-- arithmetic only; it does not identify the fifteen Ogg primes with the
-- repository's internal 5 x 3 symmetry-phase carrier.

fortyFiveIsFiveTimesThreeTimesThree : 5 * 3 * 3 ≡ 45
fortyFiveIsFiveTimesThreeTimesThree = refl

fortyFiveIsFifteenTimesThree : 15 * 3 ≡ 45
fortyFiveIsFifteenTimesThree = refl

fiftyFourIsFiveTimesNinePlusNine : 5 * 9 + 9 ≡ 54
fiftyFourIsFiveTimesNinePlusNine = refl

fiftyThreeIsFiveTimesNinePlusEight : 5 * 9 + 8 ≡ 53
fiftyThreeIsFiveTimesNinePlusEight = refl

------------------------------------------------------------------------
-- j-coarse / j-fine arithmetic, using the existing harmonic carrier owner.

jCoarse : Nat
jCoarse = Harmonic.ordinaryCoarseDimension

jFine : Nat
jFine = Harmonic.fineFrequencyDimension

jCoarseIsNine : jCoarse ≡ 9
jCoarseIsNine = refl

jFineIsThreePowerNine : jFine ≡ 19683
jFineIsThreePowerNine = refl

monsterBulk : Nat
monsterBulk = 10 * jFine

monsterBulkIs196830 : monsterBulk ≡ 196830
monsterBulkIs196830 = refl

monsterDimensionFromLocalisedBoundary : Nat
monsterDimensionFromLocalisedBoundary = monsterBulk + reducedSixByNine

monsterDimensionFromLocalisedBoundaryIs196883 :
  monsterDimensionFromLocalisedBoundary ≡ 196883
monsterDimensionFromLocalisedBoundaryIs196883 = refl

moonshineWeightTwoFromFullBoundary : Nat
moonshineWeightTwoFromFullBoundary = monsterBulk + fullSixByNine

moonshineWeightTwoFromFullBoundaryIs196884 :
  moonshineWeightTwoFromFullBoundary ≡ 196884
moonshineWeightTwoFromFullBoundaryIs196884 = refl

------------------------------------------------------------------------
-- Exact 54/56/64 ledger.  The numbers support a possible later gluing model,
-- but the interpretation is deliberately not promoted ahead of a typed
-- simplicial/cubical/hyperfabric construction.

sevenEighthsOfSixtyFour : Nat
sevenEighthsOfSixtyFour = 7 * 8

fullEightEighths : Nat
fullEightEighths = 8 * 8

sevenEighthsIsFiftySix : sevenEighthsOfSixtyFour ≡ 56
sevenEighthsIsFiftySix = refl

fullEightEighthsIsSixtyFour : fullEightEighths ≡ 64
fullEightEighthsIsSixtyFour = refl

fiftyFourPlusTwoIsFiftySix : 54 + 2 ≡ 56
fiftyFourPlusTwoIsFiftySix = refl

fiftySixPlusEightIsSixtyFour : 56 + 8 ≡ 64
fiftySixPlusEightIsSixtyFour = refl

fiftySixDeficitFromSixtyFourIsEight : 56 + 8 ≡ 64
fiftySixDeficitFromSixtyFourIsEight = refl

reducedNonaryResidualMatchesCompletionDeficit :
  reducedDistinguishedNonarySector + 56 ≡ 64
reducedNonaryResidualMatchesCompletionDeficit = refl

data GluingInterpretationBoundary : Set where
  arithmeticOnlyUntilConcreteGluingComplex : GluingInterpretationBoundary

failedGluingsLiterallyProvedHere : Bool
failedGluingsLiterallyProvedHere = false
