module DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- Hsian-Yang Chen, Ching Hung Lam and Hiroki Shimakura,
-- "Z_3-orbifold construction of the Moonshine vertex operator algebra and
-- some maximal 3-local subgroups of the Monster",
-- Mathematische Zeitschrift 288 (2018), 75--100.
-- DOI: 10.1007/s00209-017-1878-z.
--
-- Robert A. Wilson, Peter Walsh, Richard A. Parker and Stephen Linton,
-- "A computer construction of the Monster",
-- Journal of Group Theory 1 (1998), 307--337.
-- DOI: 10.1515/jgth.1998.023.
--
-- DASHI CONTRIBUTION
--
-- Replace the numerological reading
--
--   65610 = 10 * 3^8
--
-- by the normalizer-facing refinement
--
--   65610 = 3^6 * 90 = 3^6 * (12 + 78),
--
-- while proving the exact compatibility
--
--   10 * 3^8 = 90 * 3^6.
--
-- The 3^6 factor is the faithful nonlinear degree attached to a nontrivial
-- central character of an extraspecial group of order 3^(1+12).  The plus
-- and minus extraspecial types have different internal exponent/quadratic
-- geometry but the same irreducible character-degree multiset.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

threePowerSix : Nat
threePowerSix = 3 * 3 * 3 * 3 * 3 * 3

threePowerSixIs729 : threePowerSix ≡ 729
threePowerSixIs729 = refl

threePowerEight : Nat
threePowerEight = threePowerSix * 3 * 3

threePowerEightIs6561 : threePowerEight ≡ 6561
threePowerEightIs6561 = refl

extraspecialOrder : Nat
extraspecialOrder = 3 * threePowerSix * threePowerSix

extraspecialOrderIs3Power13 : extraspecialOrder ≡ 1594323
extraspecialOrderIs3Power13 = refl

symplecticQuotientOrder : Nat
symplecticQuotientOrder = threePowerSix * threePowerSix

symplecticQuotientOrderIs3Power12 :
  symplecticQuotientOrder ≡ 531441
symplecticQuotientOrderIs3Power12 = refl

------------------------------------------------------------------------
-- Plus/minus extraspecial comparison at the character-degree level.
------------------------------------------------------------------------

data ExtraspecialType : Set where
  plusType : ExtraspecialType
  minusType : ExtraspecialType

linearCharacterCount : ExtraspecialType → Nat
linearCharacterCount plusType = symplecticQuotientOrder
linearCharacterCount minusType = symplecticQuotientOrder

nonlinearCharacterCount : ExtraspecialType → Nat
nonlinearCharacterCount plusType = 2
nonlinearCharacterCount minusType = 2

nonlinearCharacterDegree : ExtraspecialType → Nat
nonlinearCharacterDegree plusType = threePowerSix
nonlinearCharacterDegree minusType = threePowerSix

characterDegreeSquareSum : ExtraspecialType → Nat
characterDegreeSquareSum kind =
  linearCharacterCount kind
  + nonlinearCharacterCount kind
    * nonlinearCharacterDegree kind
    * nonlinearCharacterDegree kind

plusCharacterDegreeSquareSumIsOrder :
  characterDegreeSquareSum plusType ≡ extraspecialOrder
plusCharacterDegreeSquareSumIsOrder = refl

minusCharacterDegreeSquareSumIsOrder :
  characterDegreeSquareSum minusType ≡ extraspecialOrder
minusCharacterDegreeSquareSumIsOrder = refl

plusMinusLinearCountsAgree :
  linearCharacterCount plusType ≡ linearCharacterCount minusType
plusMinusLinearCountsAgree = refl

plusMinusNonlinearCountsAgree :
  nonlinearCharacterCount plusType ≡ nonlinearCharacterCount minusType
plusMinusNonlinearCountsAgree = refl

plusMinusNonlinearDegreesAgree :
  nonlinearCharacterDegree plusType ≡ nonlinearCharacterDegree minusType
plusMinusNonlinearDegreesAgree = refl

------------------------------------------------------------------------
-- The documented 90-dimensional multiplicity-side count.
------------------------------------------------------------------------

naturalSuzukiDegree : Nat
naturalSuzukiDegree = 12

symmetricSquareDualDegree : Nat
symmetricSquareDualDegree = 78

multiplicityDegree : Nat
multiplicityDegree = naturalSuzukiDegree + symmetricSquareDualDegree

multiplicityDegreeIs90 : multiplicityDegree ≡ 90
multiplicityDegreeIs90 = refl

heisenbergTimesNatural : Nat
heisenbergTimesNatural = threePowerSix * naturalSuzukiDegree

heisenbergTimesNaturalIs8748 : heisenbergTimesNatural ≡ 8748
heisenbergTimesNaturalIs8748 = refl

heisenbergTimesSymmetricSquareDual : Nat
heisenbergTimesSymmetricSquareDual =
  threePowerSix * symmetricSquareDualDegree

heisenbergTimesSymmetricSquareDualIs56862 :
  heisenbergTimesSymmetricSquareDual ≡ 56862
heisenbergTimesSymmetricSquareDualIs56862 = refl

heisenbergMultiplicitySector : Nat
heisenbergMultiplicitySector = threePowerSix * multiplicityDegree

heisenbergMultiplicitySectorIs65610 :
  heisenbergMultiplicitySector ≡ 65610
heisenbergMultiplicitySectorIs65610 = refl

heisenbergBlockSplit :
  heisenbergTimesNatural + heisenbergTimesSymmetricSquareDual
  ≡ heisenbergMultiplicitySector
heisenbergBlockSplit = refl

------------------------------------------------------------------------
-- Exact overlap with the older 10 * 3^8 chart.
------------------------------------------------------------------------

tenTimesThreePowerEight : Nat
tenTimesThreePowerEight = 10 * threePowerEight

ninetyTimesThreePowerSix : Nat
ninetyTimesThreePowerSix = 90 * threePowerSix

tenTimesThreePowerEightIs65610 : tenTimesThreePowerEight ≡ 65610
tenTimesThreePowerEightIs65610 = refl

ninetyTimesThreePowerSixIs65610 : ninetyTimesThreePowerSix ≡ 65610
ninetyTimesThreePowerSixIs65610 = refl

threePowerEightIsNineHeisenbergDegrees :
  threePowerEight ≡ 9 * threePowerSix
threePowerEightIsNineHeisenbergDegrees = refl

tenByThreePowerEightEqualsNinetyByThreePowerSix :
  tenTimesThreePowerEight ≡ ninetyTimesThreePowerSix
tenByThreePowerEightEqualsNinetyByThreePowerSix = refl

------------------------------------------------------------------------
-- GF(4) versus GF(2) dimension bookkeeping from the documented restriction.
------------------------------------------------------------------------

gfFourSmallPiece : Nat
gfFourSmallPiece = 32760

gfTwoFixedPiece : Nat
gfTwoFixedPiece = 142

gfTwoMonsterModuleDegree : Nat
gfTwoMonsterModuleDegree = 196882

gfTwoDimensionReconstruction :
  gfTwoFixedPiece
  + 2 * gfFourSmallPiece
  + 2 * heisenbergMultiplicitySector
  ≡ gfTwoMonsterModuleDegree
gfTwoDimensionReconstruction = refl

ordinaryNinetySplit : naturalSuzukiDegree + symmetricSquareDualDegree ≡ 90
ordinaryNinetySplit = refl

modTwoNinetyCompositionFactorCount : 12 + 66 + 12 ≡ 90
modTwoNinetyCompositionFactorCount = refl

record HeisenbergMultiplicityBoundary : Set where
  constructor heisenbergMultiplicityBoundary
  field
    extraspecialDegreeArithmeticChecked : Bool
    extraspecialDegreeArithmeticCheckedIsTrue :
      extraspecialDegreeArithmeticChecked ≡ true
    plusMinusDegreeMultisetsAgree : Bool
    plusMinusDegreeMultisetsAgreeIsTrue :
      plusMinusDegreeMultisetsAgree ≡ true
    actualZetaSectorIsotypyCertified : Bool
    actualZetaSectorIsotypyCertifiedIsFalse :
      actualZetaSectorIsotypyCertified ≡ false
    actualMultiplicityCharacterCertified : Bool
    actualMultiplicityCharacterCertifiedIsFalse :
      actualMultiplicityCharacterCertified ≡ false
    tenTimesThreePowerEightIsPrimaryNormalizerDecomposition : Bool
    tenTimesThreePowerEightIsPrimaryNormalizerDecompositionIsFalse :
      tenTimesThreePowerEightIsPrimaryNormalizerDecomposition ≡ false
    characteristicTwoRestrictionProvesCharacteristicZeroBranching : Bool
    characteristicTwoRestrictionProvesCharacteristicZeroBranchingIsFalse :
      characteristicTwoRestrictionProvesCharacteristicZeroBranching ≡ false

canonicalHeisenbergMultiplicityBoundary : HeisenbergMultiplicityBoundary
canonicalHeisenbergMultiplicityBoundary =
  heisenbergMultiplicityBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
