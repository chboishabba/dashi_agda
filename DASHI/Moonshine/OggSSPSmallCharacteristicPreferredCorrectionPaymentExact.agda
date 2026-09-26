module DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact where

------------------------------------------------------------------------
-- PRIME-SPECIFIC PREFERRED SMALL-CHARACTERISTIC CORRECTION PAYMENT
--
-- p=2 preferred finite statistic:
--
--   five loop-reversal inertia sectors
--   weighted by v_2 of their representative centralizer orders
--
--     3, 3, 2, 1, 1
--
--   total = 10.
--
-- p=3 preferred finite statistic:
--
--   two Deligne--Rapoport local-incidence C2 orbit sectors
--   with one basis unit each
--
--     1, 1
--
--   total = 2.
--
-- This deliberately rejects a forced uniform formula across the two wild
-- primes.  The common object is only the INTERFACE: a finite local sector set
-- equipped with a prime-specific arithmetic weight.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as P2Inertia
import DASHI.Moonshine.OggSSPP2InertiaCentralizerValuationExact as P2Weight
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3
import DASHI.Moonshine.OggSSPSmallCharacteristicCorrectedValuationPaymentExact as Generic
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Generic prime-specific local payment.
------------------------------------------------------------------------

record LocalCorrectionPresentation : Set₁ where
  constructor local-correction-presentation
  field
    Sector : Set
    sectors : List Sector
    weight : Sector -> Nat
    total : Nat
    totalIsSectorWeightSum :
      total ≡ Generic.sumLocalContributions weight sectors

open LocalCorrectionPresentation public

------------------------------------------------------------------------
-- 2. p=2 preferred weighted inertia presentation.
------------------------------------------------------------------------

p2Sectors :
  List P2Inertia.BinaryTetrahedralInversionOrbit
p2Sectors =
  P2Inertia.identityInertiaOrbit
  ∷ P2Inertia.centralMinusOneInertiaOrbit
  ∷ P2Inertia.orderFourInertiaOrbit
  ∷ P2Inertia.orderThreePairInertiaOrbit
  ∷ P2Inertia.orderSixPairInertiaOrbit
  ∷ []

p2Weight :
  P2Inertia.BinaryTetrahedralInversionOrbit ->
  Nat
p2Weight =
  P2Weight.unorientedCentralizerTwoAdicDepth

p2PreferredPresentation :
  LocalCorrectionPresentation
p2PreferredPresentation =
  local-correction-presentation
    P2Inertia.BinaryTetrahedralInversionOrbit
    p2Sectors
    p2Weight
    10
    refl

p2PreferredTotalIsTen :
  total p2PreferredPresentation ≡ 10
p2PreferredTotalIsTen = refl

p2PreferredPaysMonsterGap :
  Exponent.monsterOrderExponent Lane.p2
  ≡
  Exponent.duncanSwisherExceptionalRHS Lane.p2
  + total p2PreferredPresentation
p2PreferredPaysMonsterGap =
  Exponent.p2ExceptionalGap

------------------------------------------------------------------------
-- 3. p=3 preferred local-incidence orbit presentation.
------------------------------------------------------------------------

p3Sectors :
  List P3.P3LocalOrbit
p3Sectors =
  P3.nodeOrbit
  ∷ P3.branchOrbit
  ∷ []

p3Weight :
  P3.P3LocalOrbit ->
  Nat
p3Weight P3.nodeOrbit = 1
p3Weight P3.branchOrbit = 1

p3PreferredPresentation :
  LocalCorrectionPresentation
p3PreferredPresentation =
  local-correction-presentation
    P3.P3LocalOrbit
    p3Sectors
    p3Weight
    2
    refl

p3PreferredTotalIsTwo :
  total p3PreferredPresentation ≡ 2
p3PreferredTotalIsTwo = refl

p3PreferredPaysMonsterGap :
  Exponent.monsterOrderExponent Lane.p3
  ≡
  Exponent.duncanSwisherExceptionalRHS Lane.p3
  + total p3PreferredPresentation
p3PreferredPaysMonsterGap =
  Exponent.p3ExceptionalGap

------------------------------------------------------------------------
-- 4. Unified shape, prime-specific weights.
------------------------------------------------------------------------

data WildPrime : Set where
  wildTwo wildThree : WildPrime

preferredPresentation :
  WildPrime ->
  LocalCorrectionPresentation
preferredPresentation wildTwo = p2PreferredPresentation
preferredPresentation wildThree = p3PreferredPresentation

preferredTotal :
  WildPrime ->
  Nat
preferredTotal prime =
  total (preferredPresentation prime)

preferredP2Total :
  preferredTotal wildTwo ≡ 10
preferredP2Total = refl

preferredP3Total :
  preferredTotal wildThree ≡ 2
preferredP3Total = refl

------------------------------------------------------------------------
-- 5. Analytic payment interface using the preferred prime-specific carriers.
------------------------------------------------------------------------

record PreferredCorrectedValuationAuthority : Set₁ where
  field
    AnalyticLocalTerm : Set

    p2AnalyticTerm :
      Sector p2PreferredPresentation ->
      AnalyticLocalTerm

    p3AnalyticTerm :
      Sector p3PreferredPresentation ->
      AnalyticLocalTerm

    analyticMultiplicity :
      AnalyticLocalTerm ->
      Nat

    p2WeightsAreActualLocalValuations :
      (sector : Sector p2PreferredPresentation) ->
      weight p2PreferredPresentation sector
      ≡ analyticMultiplicity (p2AnalyticTerm sector)

    p3WeightsAreActualLocalValuations :
      (sector : Sector p3PreferredPresentation) ->
      weight p3PreferredPresentation sector
      ≡ analyticMultiplicity (p3AnalyticTerm sector)

    localTermsAssembleIntoCorrectedHauptmodulValuation : Bool
    localTermsAssembleIntoCorrectedHauptmodulValuationIsTrue :
      localTermsAssembleIntoCorrectedHauptmodulValuation ≡ true

    correctedValuationPaysDuncanSwisherP2Gap : Bool
    correctedValuationPaysDuncanSwisherP2GapIsTrue :
      correctedValuationPaysDuncanSwisherP2Gap ≡ true

    correctedValuationPaysDuncanSwisherP3Gap : Bool
    correctedValuationPaysDuncanSwisherP3GapIsTrue :
      correctedValuationPaysDuncanSwisherP3Gap ≡ true

------------------------------------------------------------------------
-- 6. Firewalls.
------------------------------------------------------------------------

data PreferredFinitePaymentIsAnalyticTheorem : Set where
data PrimeSpecificWeightsCreateUniformFormula : Set where
data P2OrientationDoubletIsRequiredByPreferredWeight : Set where

preferredFinitePaymentStillNeedsAnalyticTheorem :
  PreferredFinitePaymentIsAnalyticTheorem -> ⊥
preferredFinitePaymentStillNeedsAnalyticTheorem ()

primeSpecificWeightsDoNotCreateUniformFormula :
  PrimeSpecificWeightsCreateUniformFormula -> ⊥
primeSpecificWeightsDoNotCreateUniformFormula ()

p2PreferredWeightDoesNotRequireOrientationDoublet :
  P2OrientationDoubletIsRequiredByPreferredWeight -> ⊥
p2PreferredWeightDoesNotRequireOrientationDoublet ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record PreferredCorrectionPaymentBoundary : Set where
  constructor preferred-correction-payment-boundary
  field
    p2FiveSectorCentralizerWeightsExact : Bool
    p2WeightsThreeThreeTwoOneOne : Bool
    p2TotalTen : Bool
    p3TwoLocalOrbitWeightsExact : Bool
    p3WeightsOneOne : Bool
    p3TotalTwo : Bool
    commonLocalPaymentInterfaceOwned : Bool
    oneUniformWeightFormulaAsserted : Bool
    analyticAuthorityInhabited : Bool

canonicalPreferredCorrectionPaymentBoundary :
  PreferredCorrectionPaymentBoundary
canonicalPreferredCorrectionPaymentBoundary =
  preferred-correction-payment-boundary
    true true true true true true true false false
