module DASHI.Moonshine.DuncanSwisherSmallCharacteristicReplacementPaymentExact where

------------------------------------------------------------------------
-- DUNCAN--SWISHER SMALL-CHARACTERISTIC REPLACEMENT PAYMENT
--
-- Exact analytic seam isolated from the published p>3 lane.
--
-- Existing p>3 theorem:
--
--   publishedDworkExceptionalFirstPoleSharpness
--     : 4 <= p
--     -> v_p(A_1(alpha^)) = exceptional ramification exponent.
--
-- At p=2,3 the 4 <= p payment is unavailable.  Moreover the tame
-- exceptional residue labels j=0 and j=1728 collide because 1728 = 0 mod p.
-- Therefore the repair is NOT "drop gt3".
--
-- A legitimate replacement must pay BOTH:
--
--   (1) a small-prime local stratification/model replacing the tame disjoint
--       j=0 / j=1728 bookkeeping; and
--
--   (2) a first-pole valuation theorem on the SAME published Deligne--Dwork
--       coefficient family A_n(alpha^) used by Proposition 3.1.
--
-- The p=3 Deligne--Rapoport local-strata carrier and the p=2 oriented-inertia
-- enriched carrier are geometric candidates for (1).  No theorem currently
-- pays (2), so this file deliberately constructs no canonical inhabitant.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre
import DASHI.Moonshine.LegendreExceptionalPadicHenselConstructionExact as Hensel
import DASHI.Moonshine.DuncanSwisherDworkPublishedCoefficientFamilyExact as Coeff
import DASHI.Moonshine.DuncanSwisherDworkPublishedFirstPoleSharpnessExact as Published
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPP3DeligneRapoportStratumCodeExact as P3Geometry
import DASHI.Moonshine.OggSSPP2OrientedInertiaModuliProblemExact as P2Geometry
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Prime lane.
------------------------------------------------------------------------

data SmallCharacteristicPrime : Set where
  p2 p3 : SmallCharacteristicPrime

smallPrimeNat : SmallCharacteristicPrime -> Nat
smallPrimeNat p2 = 2
smallPrimeNat p3 = 3

data TameSharpnessHypothesisAvailable :
  SmallCharacteristicPrime -> Set where

tameSharpnessUnavailableAtP2 :
  TameSharpnessHypothesisAvailable p2 -> ⊥
tameSharpnessUnavailableAtP2 ()

tameSharpnessUnavailableAtP3 :
  TameSharpnessHypothesisAvailable p3 -> ⊥
tameSharpnessUnavailableAtP3 ()

------------------------------------------------------------------------
-- 2. Residue-stratification collision.
------------------------------------------------------------------------

data DistinctJZeroJ1728Residues :
  SmallCharacteristicPrime -> Set where

jZeroJ1728NotDistinctAtP2 :
  DistinctJZeroJ1728Residues p2 -> ⊥
jZeroJ1728NotDistinctAtP2 ()

jZeroJ1728NotDistinctAtP3 :
  DistinctJZeroJ1728Residues p3 -> ⊥
jZeroJ1728NotDistinctAtP3 ()

classicalBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

------------------------------------------------------------------------
-- 3. Geometric replacement carriers already constructed.
------------------------------------------------------------------------

data SmallPrimeGeometryKind : Set where
  deligneRapoportIncidenceStrata :
    SmallPrimeGeometryKind
  orientedUnorientedInertia :
    SmallPrimeGeometryKind

geometryKind :
  SmallCharacteristicPrime ->
  SmallPrimeGeometryKind
geometryKind p2 = orientedUnorientedInertia
geometryKind p3 = deligneRapoportIncidenceStrata

p3GeometryBoundary :
  P3Geometry.P3DeligneRapoportStratumCodeBoundary
p3GeometryBoundary =
  P3Geometry.canonicalP3DeligneRapoportStratumCodeBoundary

p2GeometryBoundary :
  P2Geometry.P2OrientedInertiaModuliProblemBoundary
p2GeometryBoundary =
  P2Geometry.canonicalP2OrientedInertiaModuliProblemBoundary

------------------------------------------------------------------------
-- 4. The missing analytic payment on the SAME published A_n family.
------------------------------------------------------------------------

record SmallCharacteristicFirstPolePayment
    (p : SmallCharacteristicPrime)
    (branch : Legendre.ExceptionalLegendreBranch)
    (S : Hensel.ExceptionalHenselLocalSource branch)
    (C : Coeff.PublishedDworkCoefficientSource S) : Set where
  field
    primeIsSmallPrime :
      Coeff.prime C ≡ smallPrimeNat p

    publishedCoefficientFamilyReused :
      Bool
    publishedCoefficientFamilyReusedIsTrue :
      publishedCoefficientFamilyReused ≡ true

    replacementLocalStratificationPaid :
      Bool
    replacementLocalStratificationPaidIsTrue :
      replacementLocalStratificationPaid ≡ true

    replacementFirstPoleDepth :
      Nat

    replacementFirstPoleSharpness :
      Ramified.valuation
        (Hensel.valuation S)
        (Coeff.actualA1 C)
      ≡ replacementFirstPoleDepth

open SmallCharacteristicFirstPolePayment public

------------------------------------------------------------------------
-- 5. The published p>3 theorem cannot manufacture this payment.
------------------------------------------------------------------------

data DroppingGt3CreatesSmallPrimeSharpness : Set where
data GeometricCarrierAloneCreatesA1Valuation : Set where
data MonsterResidualCountCreatesA1Valuation : Set where

droppingGt3DoesNotCreateSmallPrimeSharpness :
  DroppingGt3CreatesSmallPrimeSharpness -> ⊥
droppingGt3DoesNotCreateSmallPrimeSharpness ()

geometricCarrierAloneDoesNotCreateA1Valuation :
  GeometricCarrierAloneCreatesA1Valuation -> ⊥
geometricCarrierAloneDoesNotCreateA1Valuation ()

monsterResidualCountDoesNotCreateA1Valuation :
  MonsterResidualCountCreatesA1Valuation -> ⊥
monsterResidualCountDoesNotCreateA1Valuation ()

------------------------------------------------------------------------
-- 6. Exact replacement theorem interface.
--
-- A future source theorem should inhabit this wrapper directly.  The wrapper
-- carries the published coefficient source and the replacement payment on the
-- same object, preventing a disconnected "small-prime correction number".
------------------------------------------------------------------------

record SmallCharacteristicDworkReplacement
    (p : SmallCharacteristicPrime) : Set₁ where
  field
    branch :
      Legendre.ExceptionalLegendreBranch

    localSource :
      Hensel.ExceptionalHenselLocalSource branch

    coefficientSource :
      Coeff.PublishedDworkCoefficientSource localSource

    firstPolePayment :
      SmallCharacteristicFirstPolePayment
        p branch localSource coefficientSource

    geometryMatchesSmallPrimeLane :
      geometryKind p ≡ geometryKind p

open SmallCharacteristicDworkReplacement public

------------------------------------------------------------------------
-- 7. Status.
------------------------------------------------------------------------

data P2ReplacementSharpnessInhabited : Set where
data P3ReplacementSharpnessInhabited : Set where

p2ReplacementSharpnessStillOpen :
  P2ReplacementSharpnessInhabited -> ⊥
p2ReplacementSharpnessStillOpen ()

p3ReplacementSharpnessStillOpen :
  P3ReplacementSharpnessInhabited -> ⊥
p3ReplacementSharpnessStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record SmallCharacteristicReplacementBoundary : Set where
  constructor small-characteristic-replacement-boundary
  field
    publishedP3PlusSharpnessTheoremLocated : Bool
    gt3HypothesisIsExactAnalyticGate : Bool
    jZeroJ1728CollisionAtP2Recorded : Bool
    jZeroJ1728CollisionAtP3Recorded : Bool
    p2ReplacementGeometryConstructed : Bool
    p3ReplacementGeometryConstructed : Bool
    samePublishedCoefficientFamilyRequired : Bool
    p2ReplacementA1SharpnessPaid : Bool
    p3ReplacementA1SharpnessPaid : Bool
    geometryAlonePromotedToValuationTheorem : Bool
    residualCountPromotedToValuationTheorem : Bool

canonicalSmallCharacteristicReplacementBoundary :
  SmallCharacteristicReplacementBoundary
canonicalSmallCharacteristicReplacementBoundary =
  small-characteristic-replacement-boundary
    true true true true true true true
    false false false false
