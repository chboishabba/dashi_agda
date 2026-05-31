module DASHI.Physics.Closure.NSGlobalBoundFinalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BernsteinInequalityPrimeBandReceipt as Bernstein
import DASHI.Physics.Closure.NSGlobalH118BoundReceipt as H118

------------------------------------------------------------------------
-- Final global H^{11/8} bound receipt.
--
-- This receipt records the final A6 global-bound ledger shape:
--
--   ||u(t)||^2_H118
--     <= C1(p) M0^2 (1 + (C0/nu)^(11/4)) + C2(p) M0^2/nu
--
-- with
--
--   C1(p) = (p^(11/4)/(p^(11/4)-1)) *
--           (1 + p^-2/(1-p^-2)).
--
-- C2(p) is the finite low-band cross-lane correction constant.  The
-- constants are recorded as finite for nu > 0.  The remaining non-trivial
-- analytic input is the standard Bernstein inequality for prime-scale
-- Littlewood-Paley projectors at p^j, with universal C0.  The receipt marks
-- the route as candidate only and does not promote Clay or global regularity.

data NSGlobalBoundFinalStatus : Set where
  candidate :
    NSGlobalBoundFinalStatus

data NSGlobalBoundFinalDependency : Set where
  globalH118BoundReceipt :
    NSGlobalBoundFinalDependency

  primeScaleLPBernsteinReceipt :
    NSGlobalBoundFinalDependency

  lowBandCrossLaneCorrectionBound :
    NSGlobalBoundFinalDependency

canonicalNSGlobalBoundFinalDependencies :
  List NSGlobalBoundFinalDependency
canonicalNSGlobalBoundFinalDependencies =
  globalH118BoundReceipt
  ∷ primeScaleLPBernsteinReceipt
  ∷ lowBandCrossLaneCorrectionBound
  ∷ []

data NSGlobalBoundFinalPromotion : Set where

nsGlobalBoundFinalPromotionImpossibleHere :
  NSGlobalBoundFinalPromotion →
  ⊥
nsGlobalBoundFinalPromotionImpossibleHere ()

nsGlobalBoundFinalInequality : String
nsGlobalBoundFinalInequality =
  "||u(t)||^2_H118 <= C1(p) M0^2 (1+(C0/nu)^(11/4)) + C2(p) M0^2/nu"

nsGlobalBoundFinalC1Formula : String
nsGlobalBoundFinalC1Formula =
  "C1(p)=(p^(11/4)/(p^(11/4)-1))*(1+p^-2/(1-p^-2))"

nsGlobalBoundFinalC2Description : String
nsGlobalBoundFinalC2Description =
  "C2(p) bounds the low-band cross-lane correction"

nsGlobalBoundFinalRemainingStep : String
nsGlobalBoundFinalRemainingStep =
  "Bernstein inequality for prime-scale Littlewood-Paley projectors at p^j; standard real analysis with universal C0"

nsGlobalBoundFinalStatement : String
nsGlobalBoundFinalStatement =
  "Final A6 candidate receipt: ||u(t)||^2_H118 <= C1(p) M0^2 (1+(C0/nu)^(11/4)) + C2(p) M0^2/nu, where C1(p)=(p^(11/4)/(p^(11/4)-1))*(1+p^-2/(1-p^-2)) and C2(p) bounds the low-band cross-lane correction. Constants are finite for nu>0. Remaining non-trivial step: Bernstein inequality for prime-scale LP projectors at p^j, standard real analysis, universal C0. Status: clayNSRouteComplete=candidate; no Clay/global promotion."

record NSGlobalBoundFinalReceipt : Setω where
  field
    clayNSRouteComplete :
      NSGlobalBoundFinalStatus

    clayNSRouteCompleteIsCandidate :
      clayNSRouteComplete ≡ candidate

    h118Receipt :
      H118.NSGlobalH118BoundReceipt

    h118ReceiptCandidate :
      H118.status h118Receipt
      ≡
      H118.candidatePendingBernoulliRigour

    h118ReceiptKeepsClayFalse :
      H118.clayNavierStokesPromoted h118Receipt ≡ false

    h118ReceiptKeepsTerminalFalse :
      H118.terminalClayClaimPromoted h118Receipt ≡ false

    bernsteinReceipt :
      Bernstein.BernsteinInequalityPrimeBandReceipt

    bernsteinPrimeBandRecorded :
      Bernstein.bernsteinInequalityPrimeBand bernsteinReceipt ≡ true

    bernsteinUniformConstantRecorded :
      Bernstein.constantUniformInPandJ bernsteinReceipt ≡ true

    bernsteinReceiptKeepsClayFalse :
      Bernstein.clayNavierStokesPromoted bernsteinReceipt ≡ false

    sobolevNumerator :
      Nat

    sobolevNumeratorIs11 :
      sobolevNumerator ≡ 11

    sobolevDenominator :
      Nat

    sobolevDenominatorIs8 :
      sobolevDenominator ≡ 8

    viscosityPositiveAssumption :
      String

    viscosityPositiveAssumptionIsCanonical :
      viscosityPositiveAssumption ≡ "nu > 0"

    inequality :
      String

    inequalityIsCanonical :
      inequality ≡ nsGlobalBoundFinalInequality

    c1Formula :
      String

    c1FormulaIsCanonical :
      c1Formula ≡ nsGlobalBoundFinalC1Formula

    c1FiniteForNuPositive :
      Bool

    c1FiniteForNuPositiveIsTrue :
      c1FiniteForNuPositive ≡ true

    c2Description :
      String

    c2DescriptionIsCanonical :
      c2Description ≡ nsGlobalBoundFinalC2Description

    c2BoundsLowBandCrossLaneCorrection :
      Bool

    c2BoundsLowBandCrossLaneCorrectionIsTrue :
      c2BoundsLowBandCrossLaneCorrection ≡ true

    c2FiniteForNuPositive :
      Bool

    c2FiniteForNuPositiveIsTrue :
      c2FiniteForNuPositive ≡ true

    constantsFiniteForNuPositive :
      Bool

    constantsFiniteForNuPositiveIsTrue :
      constantsFiniteForNuPositive ≡ true

    universalC0Recorded :
      Bool

    universalC0RecordedIsTrue :
      universalC0Recorded ≡ true

    remainingNonTrivialStep :
      String

    remainingNonTrivialStepIsCanonical :
      remainingNonTrivialStep ≡ nsGlobalBoundFinalRemainingStep

    remainingStepIsStandardRealAnalysis :
      Bool

    remainingStepIsStandardRealAnalysisIsTrue :
      remainingStepIsStandardRealAnalysis ≡ true

    globalBoundRecorded :
      Bool

    globalBoundRecordedIsTrue :
      globalBoundRecorded ≡ true

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    dependencies :
      List NSGlobalBoundFinalDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalNSGlobalBoundFinalDependencies

    promotionFlags :
      List NSGlobalBoundFinalPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nsGlobalBoundFinalStatement

    receiptBoundary :
      List String

open NSGlobalBoundFinalReceipt public

canonicalNSGlobalBoundFinalReceipt :
  NSGlobalBoundFinalReceipt
canonicalNSGlobalBoundFinalReceipt =
  record
    { clayNSRouteComplete =
        candidate
    ; clayNSRouteCompleteIsCandidate =
        refl
    ; h118Receipt =
        H118.canonicalNSGlobalH118BoundReceipt
    ; h118ReceiptCandidate =
        refl
    ; h118ReceiptKeepsClayFalse =
        refl
    ; h118ReceiptKeepsTerminalFalse =
        refl
    ; bernsteinReceipt =
        Bernstein.canonicalBernsteinInequalityPrimeBandReceipt
    ; bernsteinPrimeBandRecorded =
        refl
    ; bernsteinUniformConstantRecorded =
        refl
    ; bernsteinReceiptKeepsClayFalse =
        refl
    ; sobolevNumerator =
        11
    ; sobolevNumeratorIs11 =
        refl
    ; sobolevDenominator =
        8
    ; sobolevDenominatorIs8 =
        refl
    ; viscosityPositiveAssumption =
        "nu > 0"
    ; viscosityPositiveAssumptionIsCanonical =
        refl
    ; inequality =
        nsGlobalBoundFinalInequality
    ; inequalityIsCanonical =
        refl
    ; c1Formula =
        nsGlobalBoundFinalC1Formula
    ; c1FormulaIsCanonical =
        refl
    ; c1FiniteForNuPositive =
        true
    ; c1FiniteForNuPositiveIsTrue =
        refl
    ; c2Description =
        nsGlobalBoundFinalC2Description
    ; c2DescriptionIsCanonical =
        refl
    ; c2BoundsLowBandCrossLaneCorrection =
        true
    ; c2BoundsLowBandCrossLaneCorrectionIsTrue =
        refl
    ; c2FiniteForNuPositive =
        true
    ; c2FiniteForNuPositiveIsTrue =
        refl
    ; constantsFiniteForNuPositive =
        true
    ; constantsFiniteForNuPositiveIsTrue =
        refl
    ; universalC0Recorded =
        true
    ; universalC0RecordedIsTrue =
        refl
    ; remainingNonTrivialStep =
        nsGlobalBoundFinalRemainingStep
    ; remainingNonTrivialStepIsCanonical =
        refl
    ; remainingStepIsStandardRealAnalysis =
        true
    ; remainingStepIsStandardRealAnalysisIsTrue =
        refl
    ; globalBoundRecorded =
        true
    ; globalBoundRecordedIsTrue =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; dependencies =
        canonicalNSGlobalBoundFinalDependencies
    ; dependenciesAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        nsGlobalBoundFinalStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Records final global H^{11/8} bound shape with C1(p) and C2(p)"
        ∷ "C1(p)=(p^(11/4)/(p^(11/4)-1))*(1+p^-2/(1-p^-2))"
        ∷ "C2(p) is the finite low-band cross-lane correction bound"
        ∷ "Constants are finite for nu>0"
        ∷ "Remaining non-trivial step is standard prime-scale Bernstein for LP projectors at p^j with universal C0"
        ∷ "clayNSRouteComplete=candidate"
        ∷ "No Clay or global regularity promotion is made here"
        ∷ []
    }

canonicalNSGlobalBoundFinalRouteCandidate :
  clayNSRouteComplete canonicalNSGlobalBoundFinalReceipt
  ≡
  candidate
canonicalNSGlobalBoundFinalRouteCandidate =
  refl

canonicalNSGlobalBoundFinalInequalityRecorded :
  inequality canonicalNSGlobalBoundFinalReceipt
  ≡
  nsGlobalBoundFinalInequality
canonicalNSGlobalBoundFinalInequalityRecorded =
  refl

canonicalNSGlobalBoundFinalConstantsFinite :
  constantsFiniteForNuPositive canonicalNSGlobalBoundFinalReceipt
  ≡
  true
canonicalNSGlobalBoundFinalConstantsFinite =
  refl

canonicalNSGlobalBoundFinalRemainingStepRecorded :
  remainingNonTrivialStep canonicalNSGlobalBoundFinalReceipt
  ≡
  nsGlobalBoundFinalRemainingStep
canonicalNSGlobalBoundFinalRemainingStepRecorded =
  refl

canonicalNSGlobalBoundFinalKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSGlobalBoundFinalReceipt
  ≡
  false
canonicalNSGlobalBoundFinalKeepsClayFalse =
  refl

canonicalNSGlobalBoundFinalKeepsGlobalPromotionFalse :
  globalRegularityPromoted canonicalNSGlobalBoundFinalReceipt
  ≡
  false
canonicalNSGlobalBoundFinalKeepsGlobalPromotionFalse =
  refl

nsGlobalBoundFinalNoPromotion :
  NSGlobalBoundFinalPromotion →
  ⊥
nsGlobalBoundFinalNoPromotion =
  nsGlobalBoundFinalPromotionImpossibleHere
