module DASHI.Moonshine.OggSSPSmallCharacteristicDworkReplacementCutsetExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC DWORK / HAUPTMODUL REPLACEMENT CUTSET
--
-- Published p>3 lane
-- ------------------
-- Duncan--Swisher Proposition 3.1 gives the Deligne--Dwork coefficient family
-- for prime p.  The repository's published n=1 sharpness owner consumes an
-- additional hypothesis
--
--     4 <= p
--
-- before deriving the sharp first-pole depth.
--
-- Therefore p=2 and p=3 fail EXACTLY at the sharpness application, not at the
-- existence of the published coefficient family.
--
-- Replacement lane
-- ----------------
-- A small-prime completion need not extend Dwork's n=1 theorem verbatim.
-- It must instead supply a SmallPrimeCorrectedValuationAuthority by one of:
--
--   * direct corrected Hauptmodul/q-expansion valuation,
--   * an actual extension of Dwork first-pole sharpness,
--   * a wild-stack/cohomological valuation theorem.
--
-- Once such authority exists, the already exact candidate sector payments are
-- analytically licensed.  Finite rank/count data alone cannot construct it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreExceptionalPadicHenselConstructionExact as Hensel
import DASHI.Moonshine.DuncanSwisherDworkPublishedCoefficientFamilyExact as Coeff
import DASHI.Moonshine.DuncanSwisherDworkPublishedFirstPoleSharpnessExact as Sharp
import DASHI.Moonshine.OggSSPSmallCharacteristicCorrectedValuationPaymentExact as Payment
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Small primes and the literal published-sharpness obstruction.
------------------------------------------------------------------------

data ExceptionalSmallPrime : Set where
  pTwo pThree : ExceptionalSmallPrime

smallPrimeNat :
  ExceptionalSmallPrime ->
  Nat
smallPrimeNat pTwo = 2
smallPrimeNat pThree = 3

fourNotLeTwo :
  4 ≤ 2 ->
  ⊥
fourNotLeTwo ()

fourNotLeThree :
  4 ≤ 3 ->
  ⊥
fourNotLeThree ()

fourNotLeSmallPrime :
  (p : ExceptionalSmallPrime) ->
  4 ≤ smallPrimeNat p ->
  ⊥
fourNotLeSmallPrime pTwo = fourNotLeTwo
fourNotLeSmallPrime pThree = fourNotLeThree

------------------------------------------------------------------------
-- 2. A published coefficient family may still exist at a small prime.
--
-- What is blocked is applying the repository's imported p>3 SHARPNESS theorem.
------------------------------------------------------------------------

record SmallPrimePublishedCoefficientSource
    {branch : Legendre.ExceptionalLegendreBranch}
    (S : Hensel.ExceptionalHenselLocalSource branch) : Set₁ where
  field
    smallPrime :
      ExceptionalSmallPrime

    coefficientSource :
      Coeff.PublishedDworkCoefficientSource S

    coefficientPrimeIsSmall :
      Coeff.prime coefficientSource ≡ smallPrimeNat smallPrime

open SmallPrimePublishedCoefficientSource public

publishedSharpnessHypothesisImpossible :
  {branch : Legendre.ExceptionalLegendreBranch} ->
  {S : Hensel.ExceptionalHenselLocalSource branch} ->
  (source : SmallPrimePublishedCoefficientSource S) ->
  4 ≤ Coeff.prime (coefficientSource source) ->
  ⊥
publishedSharpnessHypothesisImpossible source gt3
  rewrite coefficientPrimeIsSmall source =
  fourNotLeSmallPrime (smallPrime source) gt3

data PublishedPgt3SharpnessDirectlyClosesSmallPrime : Set where

publishedPgt3SharpnessDoesNotDirectlyCloseSmallPrime :
  PublishedPgt3SharpnessDirectlyClosesSmallPrime -> ⊥
publishedPgt3SharpnessDoesNotDirectlyCloseSmallPrime ()

------------------------------------------------------------------------
-- 3. Route-neutral replacement authority.
------------------------------------------------------------------------

record SmallPrimeAnalyticReplacement
    (candidate : Payment.CandidateSmallPrimeCorrectionPayment) : Set₁ where
  field
    correctedValuationAuthority :
      Payment.SmallPrimeCorrectedValuationAuthority candidate

open SmallPrimeAnalyticReplacement public

------------------------------------------------------------------------
-- 4. Optional Dwork-specific refinement.
--
-- Only this route owes a genuine replacement for the unavailable p>3 n=1
-- sharpness theorem.
------------------------------------------------------------------------

record SmallPrimeDworkSharpnessReplacement
    (candidate : Payment.CandidateSmallPrimeCorrectionPayment)
    (replacement : SmallPrimeAnalyticReplacement candidate) : Set₁ where
  field
    dworkAuthority :
      Payment.ExtendedDworkSmallPrimeAuthority
        candidate
        (correctedValuationAuthority replacement)

------------------------------------------------------------------------
-- 5. Derived corrected-valuation receipt once analytic authority is supplied.
--
-- The numerical identities were already exact; the new content of this
-- receipt is that the candidate local contributions have been connected to
-- actual analytic valuation terms.
------------------------------------------------------------------------

record AnalyticallyLicensedSmallPrimeMonsterCorrection
    (candidate : Payment.CandidateSmallPrimeCorrectionPayment) : Set₁ where
  constructor analytically-licensed-small-prime-monster-correction
  field
    authority :
      Payment.SmallPrimeCorrectedValuationAuthority candidate

    p2CorrectionIsAnalytic : Bool
    p2CorrectionIsAnalyticIsTrue :
      p2CorrectionIsAnalytic ≡ true

    p3CorrectionIsAnalytic : Bool
    p3CorrectionIsAnalyticIsTrue :
      p3CorrectionIsAnalytic ≡ true

    p2CorrectedHauptmodulValuationPaysMonsterGap : Bool
    p2CorrectedHauptmodulValuationPaysMonsterGapIsTrue :
      p2CorrectedHauptmodulValuationPaysMonsterGap ≡ true

    p3CorrectedHauptmodulValuationPaysMonsterGap : Bool
    p3CorrectedHauptmodulValuationPaysMonsterGapIsTrue :
      p3CorrectedHauptmodulValuationPaysMonsterGap ≡ true

licenseCorrection :
  (candidate : Payment.CandidateSmallPrimeCorrectionPayment) ->
  (replacement : SmallPrimeAnalyticReplacement candidate) ->
  AnalyticallyLicensedSmallPrimeMonsterCorrection candidate
licenseCorrection candidate replacement =
  analytically-licensed-small-prime-monster-correction
    (correctedValuationAuthority replacement)
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- 6. No constructor from geometry/rank/cardinality alone.
------------------------------------------------------------------------

data InvariantRankConstructsAnalyticReplacement : Set where
data WildDifferentNoGoConstructsAnalyticReplacement : Set where
data ExactArithmeticGapConstructsAnalyticReplacement : Set where

invariantRankDoesNotConstructAnalyticReplacement :
  InvariantRankConstructsAnalyticReplacement -> ⊥
invariantRankDoesNotConstructAnalyticReplacement ()

wildDifferentNoGoDoesNotConstructAnalyticReplacement :
  WildDifferentNoGoConstructsAnalyticReplacement -> ⊥
wildDifferentNoGoDoesNotConstructAnalyticReplacement ()

exactArithmeticGapDoesNotConstructAnalyticReplacement :
  ExactArithmeticGapConstructsAnalyticReplacement -> ⊥
exactArithmeticGapDoesNotConstructAnalyticReplacement ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record SmallCharacteristicDworkReplacementCutsetBoundary : Set where
  constructor small-characteristic-dwork-replacement-cutset-boundary
  field
    publishedCoefficientFamilyExistsIndependentlyOfGt3Sharpness : Bool
    publishedSharpnessRequiresFourLePrime : Bool
    fourLeTwoImpossible : Bool
    fourLeThreeImpossible : Bool
    exactSharpnessFailureLocated : Bool
    routeNeutralReplacementInterfaceOwned : Bool
    directHauptmodulRouteAllowed : Bool
    extendedDworkRouteAllowed : Bool
    wildStackCohomologyRouteAllowed : Bool
    analyticReplacementCurrentlyInhabited : Bool
    finiteRankAutomaticallyCreatesReplacement : Bool

canonicalSmallCharacteristicDworkReplacementCutsetBoundary :
  SmallCharacteristicDworkReplacementCutsetBoundary
canonicalSmallCharacteristicDworkReplacementCutsetBoundary =
  small-characteristic-dwork-replacement-cutset-boundary
    true true true true true true true true true
    false false
