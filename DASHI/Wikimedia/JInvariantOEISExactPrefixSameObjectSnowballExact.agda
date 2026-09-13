module DASHI.Wikimedia.JInvariantOEISExactPrefixSameObjectSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.MoonshineModularFormCoefficientExact as Coeff
import DASHI.Wikimedia.IbrahimBase369JOEISMoonshineSnowballExact as JOEIS
import DASHI.Wikimedia.ModularFormCoefficientOEISFactorsThroughSnowballExact as Factors
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- EXACT PREFIX SAME-OBJECT WELD
--
-- External OEIS coordinates checked 2026-09-10:
--   A000521: coefficients of modular j, offset -1,
--     1, 744, 196884, 21493760, ...
--   A014708: coefficients of J=j-744 / class-1A McKay-Thompson series,
--     1, 0, 196884, 21493760, ...
--
-- The repo independently computes exactly these first four coefficients from
-- E4^3 / Delta finite convolution.  Therefore the prefix values can be welded
-- as same numerical objects at fixed exponents.  OEIS still does not supply the
-- repo's modular transformation proof or VOA/genus-zero theorems.
------------------------------------------------------------------------

data PrefixExponent : Set where
  minusOne zero one two : PrefixExponent

repoJ : PrefixExponent → Nat
repoJ minusOne = Coeff.jCoefficientMinus1
repoJ zero = Coeff.jCoefficientZero
repoJ one = Coeff.jCoefficientOne
repoJ two = Coeff.jCoefficientTwo

repoNormalizedJ : PrefixExponent → Nat
repoNormalizedJ minusOne = Coeff.normalizedJCoefficient Coeff.exponentMinusOne
repoNormalizedJ zero = Coeff.normalizedJCoefficient Coeff.exponentZero
repoNormalizedJ one = Coeff.normalizedJCoefficient Coeff.exponentOne
repoNormalizedJ two = Coeff.normalizedJCoefficient Coeff.exponentTwo

oeisA000521Prefix : PrefixExponent → Nat
oeisA000521Prefix minusOne = 1
oeisA000521Prefix zero = 744
oeisA000521Prefix one = 196884
oeisA000521Prefix two = 21493760

oeisA014708Prefix : PrefixExponent → Nat
oeisA014708Prefix minusOne = 1
oeisA014708Prefix zero = 0
oeisA014708Prefix one = 196884
oeisA014708Prefix two = 21493760

repoJMatchesA000521Prefix :
  (exponent : PrefixExponent) →
  repoJ exponent ≡ oeisA000521Prefix exponent
repoJMatchesA000521Prefix minusOne = Coeff.jMinusOneExact
repoJMatchesA000521Prefix zero = Coeff.jConstantExact
repoJMatchesA000521Prefix one = Coeff.jCoefficientOneExact
repoJMatchesA000521Prefix two = Coeff.jCoefficientTwoExact

repoNormalizedJMatchesA014708Prefix :
  (exponent : PrefixExponent) →
  repoNormalizedJ exponent ≡ oeisA014708Prefix exponent
repoNormalizedJMatchesA014708Prefix minusOne = refl
repoNormalizedJMatchesA014708Prefix zero = refl
repoNormalizedJMatchesA014708Prefix one = Coeff.jCoefficientOneExact
repoNormalizedJMatchesA014708Prefix two = Coeff.jCoefficientTwoExact

------------------------------------------------------------------------
-- External identifiers retained separately from the equality proofs.
------------------------------------------------------------------------

a000521Identity : JOEIS.OEISCoordinate
a000521Identity = JOEIS.jCoefficientOEIS

a014708Identity : JOEIS.OEISCoordinate
a014708Identity = JOEIS.class1AMcKayThompsonOEIS

record PrefixSameObjectReceipt : Set where
  constructor prefix-same-object-receipt
  field
    externalSequence : String
    normalization : String
    exponentConvention : String
    exactPrefixLength : Nat
    repoComputationIndependent : Bool
    pointwiseEqualityPaid : Bool
    transformationLawPaidByPrefix : Bool
    moonshineTheoremPaidByPrefix : Bool
open PrefixSameObjectReceipt public

jA000521Receipt : PrefixSameObjectReceipt
jA000521Receipt = prefix-same-object-receipt
  "OEIS A000521"
  "j = E4^3/Delta"
  "Laurent exponents -1,0,1,2"
  4 true true false false

normalizedJA014708Receipt : PrefixSameObjectReceipt
normalizedJA014708Receipt = prefix-same-object-receipt
  "OEIS A014708"
  "J = j - 744"
  "Laurent exponents -1,0,1,2"
  4 true true false false

------------------------------------------------------------------------
-- This sharpens FactorsThrough: prefix identity is enough for prefix queries,
-- still insufficient for full modular-object identity.
------------------------------------------------------------------------

record PrefixFactorsThroughProjection : Set where
  constructor prefix-factors-through-projection
  field
    firstFourJCoefficientsFactorThroughA000521Prefix : Bool
    firstFourNormalizedJCoefficientsFactorThroughA014708Prefix : Bool
    fullModularFormFactorsThroughFourTerms : Bool
    fullMoonshineTheoremFactorsThroughFourTerms : Bool
    failedFullFactorisationRetainsMissingAnalyticAxes : Bool
open PrefixFactorsThroughProjection public

canonicalPrefixFactorsThroughProjection : PrefixFactorsThroughProjection
canonicalPrefixFactorsThroughProjection =
  prefix-factors-through-projection true true false false true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FourTermsDetermineWholeModularForm : Set where
data OEISPrefixProvesSL2ZModularity : Set where
data NormalizedJPrefixConstructsVOA : Set where
data SharedPrefixCreatesSameInfiniteSeriesWithoutUniquenessReceipt : Set where

fourTermsDoNotDetermineWholeForm : FourTermsDetermineWholeModularForm → ⊥
fourTermsDoNotDetermineWholeForm ()

oeisPrefixDoesNotProveModularity : OEISPrefixProvesSL2ZModularity → ⊥
oeisPrefixDoesNotProveModularity ()

prefixDoesNotConstructVOA : NormalizedJPrefixConstructsVOA → ⊥
prefixDoesNotConstructVOA ()

prefixNeedsUniquenessForWholeSeries :
  SharedPrefixCreatesSameInfiniteSeriesWithoutUniquenessReceipt → ⊥
prefixNeedsUniquenessForWholeSeries ()

modularFactorsBoundary : Factors.ModularFormObservationAxes
modularFactorsBoundary = Factors.canonicalModularFormAxes

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
