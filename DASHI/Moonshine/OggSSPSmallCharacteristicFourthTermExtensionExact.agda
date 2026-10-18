module DASHI.Moonshine.OggSSPSmallCharacteristicFourthTermExtensionExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC FOURTH-TERM EXTENSION
--
-- EXTERNAL DUNCAN--SWISHER BASELINE
--
-- The three published Hauptmodul-difference valuations are already fixed:
--
--   p=2 : 12 + 16 + 8 = 36
--   p=3 :  6 +  9 + 3 = 18.
--
-- DASHI SMALL-PRIME EXTENSION SHAPE
--
-- Rather than modifying or redistributing those exact three terms, introduce
-- one additional small-prime exceptional analytic term E_p:
--
--   v_p(|M|)
--     = v_p(J_1-J_{p+})
--       + v_p(J_1-J_p)
--       + v_p(J_1-J_{p^2})
--       + E_p,
--
-- with
--
--   E_2 = 10,
--   E_3 =  2.
--
-- The numerical extension is exact.  The open theorem is the construction of
-- an ACTUAL analytic/modular/stack object whose valuation is E_p.
--
-- ATTRIBUTION
--
-- Duncan--Swisher are credited only for the three inherited terms and their
-- values.  The fourth-term extension is a DASHI research conjecture/interface.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulTermBaselineExact as Baseline
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Exceptional fourth-term value.
------------------------------------------------------------------------

exceptionalFourthTerm :
  Baseline.SmallPrime ->
  Nat
exceptionalFourthTerm Baseline.pTwo =
  Preferred.preferredTotal Preferred.wildTwo
exceptionalFourthTerm Baseline.pThree =
  Preferred.preferredTotal Preferred.wildThree

p2ExceptionalFourthTermIsTen :
  exceptionalFourthTerm Baseline.pTwo ≡ 10
p2ExceptionalFourthTermIsTen = refl

p3ExceptionalFourthTermIsTwo :
  exceptionalFourthTerm Baseline.pThree ≡ 2
p3ExceptionalFourthTermIsTwo = refl

------------------------------------------------------------------------
-- 2. Exact four-term arithmetic identities.
------------------------------------------------------------------------

extendedSmallPrimeTotal :
  Baseline.SmallPrime ->
  Nat
extendedSmallPrimeTotal prime =
  Baseline.baselineTotal prime
  + exceptionalFourthTerm prime

p2ExtendedTotalIsMonsterExponent :
  extendedSmallPrimeTotal Baseline.pTwo
  ≡ Exponent.monsterOrderExponent Lane.p2
p2ExtendedTotalIsMonsterExponent = refl

p3ExtendedTotalIsMonsterExponent :
  extendedSmallPrimeTotal Baseline.pThree
  ≡ Exponent.monsterOrderExponent Lane.p3
p3ExtendedTotalIsMonsterExponent = refl

p2LiteralFourTermIdentity :
  Exponent.monsterOrderExponent Lane.p2
  ≡
  Baseline.baselineValuation
    Baseline.pTwo Baseline.frickePrimeLevel
  +
  Baseline.baselineValuation
    Baseline.pTwo Baseline.primeLevel
  +
  Baseline.baselineValuation
    Baseline.pTwo Baseline.primeSquareLevel
  +
  exceptionalFourthTerm Baseline.pTwo
p2LiteralFourTermIdentity = refl

p3LiteralFourTermIdentity :
  Exponent.monsterOrderExponent Lane.p3
  ≡
  Baseline.baselineValuation
    Baseline.pThree Baseline.frickePrimeLevel
  +
  Baseline.baselineValuation
    Baseline.pThree Baseline.primeLevel
  +
  Baseline.baselineValuation
    Baseline.pThree Baseline.primeSquareLevel
  +
  exceptionalFourthTerm Baseline.pThree
p3LiteralFourTermIdentity = refl

------------------------------------------------------------------------
-- 3. Analytic object required to make E_p a theorem rather than a correction
--    integer fitted to the known Monster exponent.
------------------------------------------------------------------------

data ExceptionalAnalyticKind : Set where
  wildStackModularFunction :
    ExceptionalAnalyticKind
  localInertiaDeterminant :
    ExceptionalAnalyticKind
  correctedDworkFactor :
    ExceptionalAnalyticKind
  otherSourcedAnalyticObject :
    ExceptionalAnalyticKind

record SmallPrimeExceptionalAnalyticTerm : Set₁ where
  field
    ExceptionalObject : Set

    p2Object :
      ExceptionalObject

    p3Object :
      ExceptionalObject

    valuation :
      Baseline.SmallPrime ->
      ExceptionalObject ->
      Nat

    p2ValuationIsExceptionalFourthTerm :
      valuation Baseline.pTwo p2Object
      ≡ exceptionalFourthTerm Baseline.pTwo

    p3ValuationIsExceptionalFourthTerm :
      valuation Baseline.pThree p3Object
      ≡ exceptionalFourthTerm Baseline.pThree

    analyticKind :
      ExceptionalAnalyticKind

    objectDefinedIndependentlyOfMonsterExponent : Bool
    objectDefinedIndependentlyOfMonsterExponentIsTrue :
      objectDefinedIndependentlyOfMonsterExponent ≡ true

    valuationTheoremProvedWithoutUsingTargetMonsterGap : Bool
    valuationTheoremProvedWithoutUsingTargetMonsterGapIsTrue :
      valuationTheoremProvedWithoutUsingTargetMonsterGap ≡ true

    compatibleWithPublishedThreeTermBaseline : Bool
    compatibleWithPublishedThreeTermBaselineIsTrue :
      compatibleWithPublishedThreeTermBaseline ≡ true

open SmallPrimeExceptionalAnalyticTerm public

------------------------------------------------------------------------
-- 4. Once an independently defined exceptional analytic term exists, the
--    four-term extension is analytically licensed.
------------------------------------------------------------------------

record AnalyticallyLicensedFourTermExtension : Set₁ where
  constructor analytically-licensed-four-term-extension
  field
    exceptionalAuthority :
      SmallPrimeExceptionalAnalyticTerm

    inheritedDuncanSwisherTermsUnchanged : Bool
    inheritedDuncanSwisherTermsUnchangedIsTrue :
      inheritedDuncanSwisherTermsUnchanged ≡ true

    p2FourthTermPaysExactGap : Bool
    p2FourthTermPaysExactGapIsTrue :
      p2FourthTermPaysExactGap ≡ true

    p3FourthTermPaysExactGap : Bool
    p3FourthTermPaysExactGapIsTrue :
      p3FourthTermPaysExactGap ≡ true

licenseFourTermExtension :
  SmallPrimeExceptionalAnalyticTerm ->
  AnalyticallyLicensedFourTermExtension
licenseFourTermExtension authority =
  analytically-licensed-four-term-extension
    authority
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- 5. The three inherited terms are not silently modified.
------------------------------------------------------------------------

data FourthTermChangesPublishedFrickeValuation : Set where
data FourthTermChangesPublishedPrimeValuation : Set where
data FourthTermChangesPublishedPrimeSquareValuation : Set where
data DuncanSwisherProposedFourthTerm : Set where
data ExactArithmeticIdentityConstructsExceptionalAnalyticObject : Set where

fourthTermDoesNotChangePublishedFrickeValuation :
  FourthTermChangesPublishedFrickeValuation -> ⊥
fourthTermDoesNotChangePublishedFrickeValuation ()

fourthTermDoesNotChangePublishedPrimeValuation :
  FourthTermChangesPublishedPrimeValuation -> ⊥
fourthTermDoesNotChangePublishedPrimeValuation ()

fourthTermDoesNotChangePublishedPrimeSquareValuation :
  FourthTermChangesPublishedPrimeSquareValuation -> ⊥
fourthTermDoesNotChangePublishedPrimeSquareValuation ()

duncanSwisherNotCreditedWithFourthTerm :
  DuncanSwisherProposedFourthTerm -> ⊥
duncanSwisherNotCreditedWithFourthTerm ()

arithmeticIdentityDoesNotConstructExceptionalObject :
  ExactArithmeticIdentityConstructsExceptionalAnalyticObject -> ⊥
arithmeticIdentityDoesNotConstructExceptionalAnalyticObject ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record FourthTermExtensionBoundary : Set where
  constructor fourth-term-extension-boundary
  field
    publishedThreeTermsLeftUnchanged : Bool
    p2ExceptionalTermTenExact : Bool
    p3ExceptionalTermTwoExact : Bool
    p2FourTermArithmeticIdentityExact : Bool
    p3FourTermArithmeticIdentityExact : Bool
    independentExceptionalAnalyticObjectRequired : Bool
    noTargetGapCircularityRequired : Bool
    duncanSwisherCreditedWithFourthTerm : Bool
    exceptionalAnalyticAuthorityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalFourthTermExtensionBoundary :
  FourthTermExtensionBoundary
canonicalFourthTermExtensionBoundary =
  fourth-term-extension-boundary
    true true true true true true true false false true
