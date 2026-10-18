module DASHI.Moonshine.OggSSP2BIntegralTateTraceValuationAuditExact where

------------------------------------------------------------------------
-- 2B INTEGRAL TATE-TRACE VALUATION AUDIT
--
-- EXTERNAL SOURCE
--
-- Carnahan Corollary 3.25 gives, for g=2B:
--
--   H0 trace = ( T_g(tau) + T_g(tau+1/2) ) / 2
--   H1 trace = ( T_g(tau) - T_g(tau+1/2) ) / 2.
--
-- The normalized 2B McKay--Thompson series begins:
--
--   T_2B =
--     q^-1 + 276q - 2048q^2 + 11202q^3 - 49152q^4 + ...
--
-- Since tau -> tau+1/2 sends q -> -q, the integral Tate pieces split by
-- q-exponent parity:
--
--   H0 = -2048q^2 - 49152q^4 + ...
--   H1 = q^-1 + 276q + 11202q^3 + ...
--
-- DASHI AUDIT
--
--   v2(2048)  = 11,
--   v2(49152) = 14,
--   v2(276)   = 2,
--   v2(11202) = 1.
--
-- Hence neither the first H0 coefficient depth (11) nor the first positive H1
-- coefficient depth (2) equals the independent p=2 Monster-local residual 10.
--
-- As at p=3, the missing fourth term must be a derived bad-level/localized
-- observable, not a raw integral Tate coefficient valuation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact as Local
import DASHI.Moonshine.OggSSP2B3BPadicAnnihilationSlopeComparisonExact as Slope
import DASHI.Moonshine.OggSSPSmallPrimePBIntegralTateCohomologyBridgeExact as Tate
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution.
------------------------------------------------------------------------

carnahanIntegralForm : Source.AttributedSource
carnahanIntegralForm =
  Source.mkDOISource
    "Scott Carnahan"
    "A Self-Dual Integral Form of the Moonshine Module"
    "SIGMA 15 (2019), 030"
    "2019"
    "10.3842/SIGMA.2019.030"
    "https://doi.org/10.3842/SIGMA.2019.030"
    Source.academicArticleSource
    "Corollary 3.25 gives the unconditional 2B Tate H0/H1 half-translation formulas on the Monster-stable self-dual integral form"
    Source.publicAttribution

twoBHauptmodulSource : Source.AttributedSource
twoBHauptmodulSource =
  Source.mkNoDOISource
    "standard monstrous moonshine tables"
    "McKay--Thompson series for Monster class 2B"
    "standard moonshine / eta-quotient presentation"
    ""
    "https://oeis.org/A007191"
    Source.institutionalSource
    "records the 2B series coefficients used in the displayed prefix audit; the underlying eta-quotient identity is standard and independently sourced elsewhere in the repository"
    Source.publicAttribution

twoBTateTraceValuationAtlas : Source.AttributedSourceAtlas
twoBTateTraceValuationAtlas =
  Source.mkSourceAtlas
    "2B integral Tate-trace valuation audit"
    "DASHI.Moonshine.OggSSP2BIntegralTateTraceValuationAuditExact"
    (carnahanIntegralForm ∷ twoBHauptmodulSource ∷ [])
    "Carnahan owns the integral Tate formula and standard moonshine sources own the 2B q-series; DASHI owns the finite 2-adic audit against the independent residual ten"

------------------------------------------------------------------------
-- 2. Displayed source coefficients after parity splitting.
------------------------------------------------------------------------

data EvenDisplayedDegree : Set where
  q2 q4 : EvenDisplayedDegree

data OddDisplayedDegree : Set where
  q1 q3 : OddDisplayedDegree

h0EvenCoefficientMagnitude :
  EvenDisplayedDegree ->
  Nat
h0EvenCoefficientMagnitude q2 = 2048
h0EvenCoefficientMagnitude q4 = 49152

h1OddCoefficientMagnitude :
  OddDisplayedDegree ->
  Nat
h1OddCoefficientMagnitude q1 = 276
h1OddCoefficientMagnitude q3 = 11202

h0TwoAdicDepth :
  EvenDisplayedDegree ->
  Nat
h0TwoAdicDepth q2 = 11
h0TwoAdicDepth q4 = 14

h1TwoAdicDepth :
  OddDisplayedDegree ->
  Nat
h1TwoAdicDepth q1 = 2
h1TwoAdicDepth q3 = 1

h0Q2DepthIsEleven :
  h0TwoAdicDepth q2 ≡ 11
h0Q2DepthIsEleven = refl

h0Q4DepthIsFourteen :
  h0TwoAdicDepth q4 ≡ 14
h0Q4DepthIsFourteen = refl

h1Q1DepthIsTwo :
  h1TwoAdicDepth q1 ≡ 2
h1Q1DepthIsTwo = refl

h1Q3DepthIsOne :
  h1TwoAdicDepth q3 ≡ 1
h1Q3DepthIsOne = refl

------------------------------------------------------------------------
-- 3. Compare raw Tate depths with the independent p=2 residual.
------------------------------------------------------------------------

h0FirstVisibleDepth : Nat
h0FirstVisibleDepth =
  h0TwoAdicDepth q2

h1FirstPositiveDepth : Nat
h1FirstPositiveDepth =
  h1TwoAdicDepth q1

h0FirstVisibleDepthNotResidualTen :
  h0FirstVisibleDepth
  ≡ Local.p2LocalCentralizerResidual
  ->
  ⊥
h0FirstVisibleDepthNotResidualTen ()

h1FirstPositiveDepthNotResidualTen :
  h1FirstPositiveDepth
  ≡ Local.p2LocalCentralizerResidual
  ->
  ⊥
h1FirstPositiveDepthNotResidualTen ()

------------------------------------------------------------------------
-- 4. CMT eventual increment is yet another observable.
------------------------------------------------------------------------

cmtObservedTwoBIncrement : Nat
cmtObservedTwoBIncrement =
  Slope.eventualIncrement Slope.class2BAt2

cmtObservedTwoBIncrementIsThree :
  cmtObservedTwoBIncrement ≡ 3
cmtObservedTwoBIncrementIsThree = refl

cmtObservedTwoBIncrementNotResidualTen :
  cmtObservedTwoBIncrement
  ≡ Local.p2LocalCentralizerResidual
  ->
  ⊥
cmtObservedTwoBIncrementNotResidualTen ()

h0RawDepthNotCMTIncrement :
  h0FirstVisibleDepth
  ≡ cmtObservedTwoBIncrement
  ->
  ⊥
h0RawDepthNotCMTIncrement ()

------------------------------------------------------------------------
-- 5. Firewalls.
------------------------------------------------------------------------

data RawTwoBTateCoefficientDepthIsFourthTerm : Set where
data EvenOddParitySplitExplainsResidualTen : Set where
data DisplayedPrefixProvesFullTateSeriesValuation : Set where
data CarnahanCreditedWithResidualTen : Set where

rawTwoBTateDepthIsNotFourthTerm :
  RawTwoBTateCoefficientDepthIsFourthTerm -> ⊥
rawTwoBTateDepthIsNotFourthTerm ()

paritySplitAloneDoesNotExplainResidualTen :
  EvenOddParitySplitExplainsResidualTen -> ⊥
paritySplitAloneDoesNotExplainResidualTen ()

displayedPrefixDoesNotProveFullTateSeriesValuation :
  DisplayedPrefixProvesFullTateSeriesValuation -> ⊥
displayedPrefixDoesNotProveFullTateSeriesValuation ()

carnahanNotCreditedWithResidualTen :
  CarnahanCreditedWithResidualTen -> ⊥
carnahanNotCreditedWithResidualTen ()

------------------------------------------------------------------------
-- 6. Live boundary.
------------------------------------------------------------------------

integralTateBoundary :
  Tate.PBIntegralTateBridgeBoundary
integralTateBoundary =
  Tate.canonicalPBIntegralTateBridgeBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record TwoBIntegralTateTraceValuationAuditBoundary : Set where
  constructor twoB-integral-tate-trace-valuation-audit-boundary
  field
    carnahanTwoBTateFormulaSourced : Bool
    twoBHauptmodulPrefixSourced : Bool
    paritySplitConstructed : Bool
    displayedPrefixTwoAdicDepthsAudited : Bool
    h0FirstDepthEleven : Bool
    h1FirstPositiveDepthTwo : Bool
    rawH0DepthMatchesResidualTen : Bool
    rawH1DepthMatchesResidualTen : Bool
    cmtObservedIncrementThreeRecorded : Bool
    cmtIncrementMatchesResidualTen : Bool
    rawCoefficientShortcutRejected : Bool
    displayedPrefixPromotedToFullSeriesTheorem : Bool
    attributionFirewallPreserved : Bool

canonicalTwoBIntegralTateTraceValuationAuditBoundary :
  TwoBIntegralTateTraceValuationAuditBoundary
canonicalTwoBIntegralTateTraceValuationAuditBoundary =
  twoB-integral-tate-trace-valuation-audit-boundary
    true true true true true true false false true false true false true
