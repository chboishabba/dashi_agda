module DASHI.Moonshine.OggSSPSmallCharacteristicCorrectedValuationPaymentExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC CORRECTED MODULAR-VALUATION PAYMENT
--
-- EXTERNAL ARITHMETIC INPUT
--
-- Duncan--Swisher, Theorem 1.1:
--
--   v_p(|M|)
--     = v_p(J_1-J_{p+})
--       + v_p(J_1-J_p)
--       + v_p(J_1-J_{p^2})
--
-- for p > 3.
--
-- Their Remark 1.3 computes the same right-hand side at the exceptional
-- primes:
--
--   p=2 : 36, while v_2(|M|)=46,
--   p=3 : 18, while v_3(|M|)=20.
--
-- Hence any successful small-prime extension must supply an additional
-- valuation-theoretic payment of 10 and 2 respectively.
--
-- DASHI CANDIDATE
--
-- The classically grounded wild carriers constructed upstream have exactly:
--
--   p=2 : ten enriched orientation x unoriented-inertia sectors,
--   p=3 : two local-incidence C2 orbit sectors.
--
-- This module does MORE than equate cardinalities: it constructs explicit
-- sector-wise candidate contribution functions c_p(sigma)=1 and computes their
-- finite sums to 10 and 2.
--
-- It deliberately does NOT promote that candidate to an analytic theorem.
-- A genuine completion must prove that the local terms arise from the corrected
-- integral q-expansion / Dwork / Hauptmodul valuation mechanism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution
import DASHI.Moonshine.OggSSPP2OrientedInertiaModuliProblemExact as P2
import DASHI.Moonshine.OggSSPP2OrientedInertiaTenStateRecognitionExact as P2Ten
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as P2Inertia
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3

------------------------------------------------------------------------
-- 1. Generic finite local-contribution sum.
------------------------------------------------------------------------

sumLocalContributions :
  {Sector : Set} ->
  (Sector -> Nat) ->
  List Sector ->
  Nat
sumLocalContributions contribution [] = 0
sumLocalContributions contribution (sector ∷ rest) =
  contribution sector + sumLocalContributions contribution rest

unitContribution :
  {Sector : Set} ->
  Sector ->
  Nat
unitContribution sector = 1

------------------------------------------------------------------------
-- 2. p=3 two local-incidence orbit sectors.
------------------------------------------------------------------------

p3WildSectors : List P3.P3LocalOrbit
p3WildSectors =
  P3.nodeOrbit
  ∷ P3.branchOrbit
  ∷ []

p3CandidateLocalContribution :
  P3.P3LocalOrbit ->
  Nat
p3CandidateLocalContribution =
  unitContribution

p3CandidateWildCorrection : Nat
p3CandidateWildCorrection =
  sumLocalContributions
    p3CandidateLocalContribution
    p3WildSectors

p3CandidateWildCorrectionIsTwo :
  p3CandidateWildCorrection ≡ 2
p3CandidateWildCorrectionIsTwo = refl

p3CandidateCorrectionPaysExactMonsterGap :
  Exponent.monsterOrderExponent Lane.p3
  ≡
  Exponent.duncanSwisherExceptionalRHS Lane.p3
  + p3CandidateWildCorrection
p3CandidateCorrectionPaysExactMonsterGap =
  Exponent.p3ExceptionalGap

------------------------------------------------------------------------
-- 3. p=2 ten enriched sectors.
------------------------------------------------------------------------

p2WildSectors : List P2.P2EnrichedSector
p2WildSectors =
  P2.p2-enriched-sector
    P2Ten.firstGaloisOrientation
    P2Inertia.identityInertiaOrbit
  ∷ P2.p2-enriched-sector
    P2Ten.firstGaloisOrientation
    P2Inertia.centralMinusOneInertiaOrbit
  ∷ P2.p2-enriched-sector
    P2Ten.firstGaloisOrientation
    P2Inertia.orderFourInertiaOrbit
  ∷ P2.p2-enriched-sector
    P2Ten.firstGaloisOrientation
    P2Inertia.orderThreePairInertiaOrbit
  ∷ P2.p2-enriched-sector
    P2Ten.firstGaloisOrientation
    P2Inertia.orderSixPairInertiaOrbit
  ∷ P2.p2-enriched-sector
    P2Ten.conjugateGaloisOrientation
    P2Inertia.identityInertiaOrbit
  ∷ P2.p2-enriched-sector
    P2Ten.conjugateGaloisOrientation
    P2Inertia.centralMinusOneInertiaOrbit
  ∷ P2.p2-enriched-sector
    P2Ten.conjugateGaloisOrientation
    P2Inertia.orderFourInertiaOrbit
  ∷ P2.p2-enriched-sector
    P2Ten.conjugateGaloisOrientation
    P2Inertia.orderThreePairInertiaOrbit
  ∷ P2.p2-enriched-sector
    P2Ten.conjugateGaloisOrientation
    P2Inertia.orderSixPairInertiaOrbit
  ∷ []

p2CandidateLocalContribution :
  P2.P2EnrichedSector ->
  Nat
p2CandidateLocalContribution =
  unitContribution

p2CandidateWildCorrection : Nat
p2CandidateWildCorrection =
  sumLocalContributions
    p2CandidateLocalContribution
    p2WildSectors

p2CandidateWildCorrectionIsTen :
  p2CandidateWildCorrection ≡ 10
p2CandidateWildCorrectionIsTen = refl

p2CandidateCorrectionPaysExactMonsterGap :
  Exponent.monsterOrderExponent Lane.p2
  ≡
  Exponent.duncanSwisherExceptionalRHS Lane.p2
  + p2CandidateWildCorrection
p2CandidateCorrectionPaysExactMonsterGap =
  Exponent.p2ExceptionalGap

------------------------------------------------------------------------
-- 4. Candidate payment package.
------------------------------------------------------------------------

record CandidateSmallPrimeCorrectionPayment : Set₁ where
  constructor candidate-small-prime-correction-payment
  field
    P2Sector : Set
    P3Sector : Set

    p2Contribution :
      P2Sector -> Nat
    p3Contribution :
      P3Sector -> Nat

    p2Enumeration :
      List P2Sector
    p3Enumeration :
      List P3Sector

    p2Total :
      Nat
    p3Total :
      Nat

    p2TotalIsFiniteSectorSum :
      p2Total
      ≡ sumLocalContributions p2Contribution p2Enumeration

    p3TotalIsFiniteSectorSum :
      p3Total
      ≡ sumLocalContributions p3Contribution p3Enumeration

    p2TotalIsExceptionalGap :
      Exponent.monsterOrderExponent Lane.p2
      ≡ Exponent.duncanSwisherExceptionalRHS Lane.p2 + p2Total

    p3TotalIsExceptionalGap :
      Exponent.monsterOrderExponent Lane.p3
      ≡ Exponent.duncanSwisherExceptionalRHS Lane.p3 + p3Total

open CandidateSmallPrimeCorrectionPayment public

canonicalCandidateSmallPrimeCorrectionPayment :
  CandidateSmallPrimeCorrectionPayment
canonicalCandidateSmallPrimeCorrectionPayment =
  candidate-small-prime-correction-payment
    P2.P2EnrichedSector
    P3.P3LocalOrbit
    p2CandidateLocalContribution
    p3CandidateLocalContribution
    p2WildSectors
    p3WildSectors
    p2CandidateWildCorrection
    p3CandidateWildCorrection
    refl
    refl
    p2CandidateCorrectionPaysExactMonsterGap
    p3CandidateCorrectionPaysExactMonsterGap

------------------------------------------------------------------------
-- 5. Analytic authority required to turn the candidate into a theorem.
--
-- The key new payment is not another count.  It is the theorem that each
-- c_p(sigma) is an actual local term in a corrected modular-function valuation.
------------------------------------------------------------------------

record SmallPrimeCorrectedValuationAuthority
    (candidate : CandidateSmallPrimeCorrectionPayment) : Set₁ where
  field
    CorrectedLocalValuationTerm : Set

    p2AnalyticLocalTerm :
      P2Sector candidate ->
      CorrectedLocalValuationTerm

    p3AnalyticLocalTerm :
      P3Sector candidate ->
      CorrectedLocalValuationTerm

    valuationMultiplicity :
      CorrectedLocalValuationTerm ->
      Nat

    p2CandidateContributionIsAnalytic :
      (sector : P2Sector candidate) ->
      p2Contribution candidate sector
      ≡ valuationMultiplicity (p2AnalyticLocalTerm sector)

    p3CandidateContributionIsAnalytic :
      (sector : P3Sector candidate) ->
      p3Contribution candidate sector
      ≡ valuationMultiplicity (p3AnalyticLocalTerm sector)

    correctedQExpansionValuationTheorem : Bool
    correctedQExpansionValuationTheoremIsTrue :
      correctedQExpansionValuationTheorem ≡ true

    correctedDworkFirstPoleSharpnessAtP2 : Bool
    correctedDworkFirstPoleSharpnessAtP2IsTrue :
      correctedDworkFirstPoleSharpnessAtP2 ≡ true

    correctedDworkFirstPoleSharpnessAtP3 : Bool
    correctedDworkFirstPoleSharpnessAtP3IsTrue :
      correctedDworkFirstPoleSharpnessAtP3 ≡ true

    localTermsAssembleToHauptmodulDifferenceValuation : Bool
    localTermsAssembleToHauptmodulDifferenceValuationIsTrue :
      localTermsAssembleToHauptmodulDifferenceValuation ≡ true

------------------------------------------------------------------------
-- 6. No fake constructor from finite geometry alone.
------------------------------------------------------------------------

data SectorEnumerationCreatesCorrectedValuationAuthority : Set where
data UnitWeightsCreateCorrectedValuationAuthority : Set where
data ExactGapEqualityCreatesCorrectedValuationAuthority : Set where

sectorEnumerationDoesNotCreateAnalyticAuthority :
  SectorEnumerationCreatesCorrectedValuationAuthority -> ⊥
sectorEnumerationDoesNotCreateAnalyticAuthority ()

unitWeightsDoNotCreateAnalyticAuthority :
  UnitWeightsCreateCorrectedValuationAuthority -> ⊥
unitWeightsDoNotCreateAnalyticAuthority ()

exactGapEqualityDoesNotCreateAnalyticAuthority :
  ExactGapEqualityCreatesCorrectedValuationAuthority -> ⊥
exactGapEqualityDoesNotCreateAnalyticAuthority ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record CorrectedValuationPaymentBoundary : Set where
  constructor corrected-valuation-payment-boundary
  field
    p2ExplicitTenSectorEnumerationConstructed : Bool
    p3ExplicitTwoOrbitEnumerationConstructed : Bool
    p2UnitContributionSumIsTen : Bool
    p3UnitContributionSumIsTwo : Bool
    p2CandidatePaysExactArithmeticGap : Bool
    p3CandidatePaysExactArithmeticGap : Bool
    analyticLocalTermAuthorityConstructed : Bool
    correctedQExpansionTheoremConstructed : Bool
    correctedP2DworkSharpnessConstructed : Bool
    correctedP3DworkSharpnessConstructed : Bool
    finiteCountPromotedToAnalyticValuation : Bool

canonicalCorrectedValuationPaymentBoundary :
  CorrectedValuationPaymentBoundary
canonicalCorrectedValuationPaymentBoundary =
  corrected-valuation-payment-boundary
    true true true true true true
    false false false false false
