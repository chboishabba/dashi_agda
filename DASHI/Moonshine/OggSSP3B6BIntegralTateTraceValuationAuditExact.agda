module DASHI.Moonshine.OggSSP3B6BIntegralTateTraceValuationAuditExact where

------------------------------------------------------------------------
-- 3B / 6B INTEGRAL TATE-TRACE VALUATION AUDIT
--
-- EXTERNAL SOURCE
--
-- Borcherds, "Modular Moonshine III", for g in Monster class 3B:
--
--   T_3B =
--     q^-1 + 54q - 76q^2 - 243q^3 + 1188q^4 - 1384q^5 - ...
--
-- and the distinguished involution companion sigma*g is Monster class 6B:
--
--   T_6B =
--     q^-1 + 78q + 364q^2 + 1365q^3 + 4380q^4 + 12520q^5 + ...
--
-- Hence the ordinary/super Tate pieces are explicitly:
--
--   H0 = (T_3B + T_6B)/2
--      = q^-1 + 66q + 144q^2 + 561q^3 + 2784q^4 + 5568q^5 + ...
--
--   H1 = (T_6B - T_3B)/2
--      = 12q + 220q^2 + 804q^3 + 1596q^4 + 6952q^5 + ...
--
-- Carnahan's Corollary 3.25 upgrades modular moonshine to an unconditional
-- self-dual integral Moonshine form and Tate-cohomology Brauer-character
-- formula.  We therefore treat these as source-backed coefficients of the
-- integral/mod-3 pB centralizer object.
--
-- DASHI AUDIT
--
-- On the displayed prefix:
--
--   v3(H0_q)  = 1
--   v3(H0_q2) = 2
--   v3(H0_q3) = 1
--   v3(H0_q4) = 1
--   v3(H0_q5) = 1
--
--   v3(H1_q)  = 1
--   v3(H1_q2) = 0
--   v3(H1_q3) = 1
--   v3(H1_q4) = 1
--   v3(H1_q5) = 0.
--
-- In particular the first coefficient visible after U_3, the q^3
-- coefficient, has valuation 1 in BOTH Tate parities, not the independent
-- Monster-local residual 2.
--
-- This rejects the shortcut
--
--   "raw integral Tate coefficient valuation = exceptional fourth term".
--
-- It does NOT contradict the CMT numerical annihilation pattern 5 -> 2:
-- that 2 is an eventual U_3 valuation INCREMENT, a different observable.
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

borcherdsModularMoonshineIII : Source.AttributedSource
borcherdsModularMoonshineIII =
  Source.mkDOISource
    "Richard E. Borcherds"
    "Modular Moonshine III"
    "Duke Mathematical Journal 93(1), 129-154"
    "1998"
    "10.1215/S0012-7094-98-09305-X"
    "https://doi.org/10.1215/S0012-7094-98-09305-X"
    Source.academicArticleSource
    "for g=3B identifies the distinguished involution companion sigma*g as Monster class 6B and explicitly gives T_3B, T_6B, and the resulting ordinary/super modular-moonshine q-series coefficients; used here as coefficient-level source authority"
    Source.publicAttribution

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
    "Corollary 3.25 makes the modular-moonshine Tate-cohomology Brauer-character formulas unconditional for a Monster-stable self-dual integral form; does not state the DASHI 3-adic valuation audit"
    Source.publicAttribution

tateTraceValuationAuditAtlas : Source.AttributedSourceAtlas
tateTraceValuationAuditAtlas =
  Source.mkSourceAtlas
    "3B/6B integral Tate-trace valuation audit"
    "DASHI.Moonshine.OggSSP3B6BIntegralTateTraceValuationAuditExact"
    (borcherdsModularMoonshineIII ∷ carnahanIntegralForm ∷ [])
    "Borcherds/Carnahan own the class identification and Tate q-series; DASHI owns the finite 3-adic valuation comparison against the independently defined local residual"

------------------------------------------------------------------------
-- 2. Exact sourced positive q-coefficient magnitudes.
------------------------------------------------------------------------

data DisplayedDegree : Set where
  q1 q2 q3 q4 q5 : DisplayedDegree

ordinaryCoefficientMagnitude :
  DisplayedDegree ->
  Nat
ordinaryCoefficientMagnitude q1 = 66
ordinaryCoefficientMagnitude q2 = 144
ordinaryCoefficientMagnitude q3 = 561
ordinaryCoefficientMagnitude q4 = 2784
ordinaryCoefficientMagnitude q5 = 5568

superCoefficientMagnitude :
  DisplayedDegree ->
  Nat
superCoefficientMagnitude q1 = 12
superCoefficientMagnitude q2 = 220
superCoefficientMagnitude q3 = 804
superCoefficientMagnitude q4 = 1596
superCoefficientMagnitude q5 = 6952

------------------------------------------------------------------------
-- 3. Exact 3-adic depths on the displayed prefix.
--
-- These values are direct arithmetic audits of the sourced coefficients.
------------------------------------------------------------------------

ordinaryThreeAdicDepth :
  DisplayedDegree ->
  Nat
ordinaryThreeAdicDepth q1 = 1
ordinaryThreeAdicDepth q2 = 2
ordinaryThreeAdicDepth q3 = 1
ordinaryThreeAdicDepth q4 = 1
ordinaryThreeAdicDepth q5 = 1

superThreeAdicDepth :
  DisplayedDegree ->
  Nat
superThreeAdicDepth q1 = 1
superThreeAdicDepth q2 = 0
superThreeAdicDepth q3 = 1
superThreeAdicDepth q4 = 1
superThreeAdicDepth q5 = 0

ordinaryQ1DepthIsOne :
  ordinaryThreeAdicDepth q1 ≡ 1
ordinaryQ1DepthIsOne = refl

ordinaryQ2DepthIsTwo :
  ordinaryThreeAdicDepth q2 ≡ 2
ordinaryQ2DepthIsTwo = refl

ordinaryQ3DepthIsOne :
  ordinaryThreeAdicDepth q3 ≡ 1
ordinaryQ3DepthIsOne = refl

superQ2DepthIsZero :
  superThreeAdicDepth q2 ≡ 0
superQ2DepthIsZero = refl

superQ3DepthIsOne :
  superThreeAdicDepth q3 ≡ 1
superQ3DepthIsOne = refl

superQ5DepthIsZero :
  superThreeAdicDepth q5 ≡ 0
superQ5DepthIsZero = refl

------------------------------------------------------------------------
-- 4. First U_3-visible coefficient audit.
------------------------------------------------------------------------

ordinaryFirstU3VisibleDepth : Nat
ordinaryFirstU3VisibleDepth =
  ordinaryThreeAdicDepth q3

superFirstU3VisibleDepth : Nat
superFirstU3VisibleDepth =
  superThreeAdicDepth q3

ordinaryFirstU3VisibleDepthIsOne :
  ordinaryFirstU3VisibleDepth ≡ 1
ordinaryFirstU3VisibleDepthIsOne = refl

superFirstU3VisibleDepthIsOne :
  superFirstU3VisibleDepth ≡ 1
superFirstU3VisibleDepthIsOne = refl

ordinaryFirstU3VisibleDepthNotResidualTwo :
  ordinaryFirstU3VisibleDepth
  ≡ Local.p3LocalCentralizerResidual
  ->
  ⊥
ordinaryFirstU3VisibleDepthNotResidualTwo ()

superFirstU3VisibleDepthNotResidualTwo :
  superFirstU3VisibleDepth
  ≡ Local.p3LocalCentralizerResidual
  ->
  ⊥
superFirstU3VisibleDepthNotResidualTwo ()

------------------------------------------------------------------------
-- 5. Distinguish raw coefficient depth from CMT eventual U_3 increment.
------------------------------------------------------------------------

cmtObservedThreeBIncrement : Nat
cmtObservedThreeBIncrement =
  Slope.eventualIncrement Slope.class3BAt3

cmtObservedThreeBIncrementIsTwo :
  cmtObservedThreeBIncrement ≡ 2
cmtObservedThreeBIncrementIsTwo = refl

cmtObservedThreeBIncrementMatchesResidual :
  cmtObservedThreeBIncrement
  ≡ Local.p3LocalCentralizerResidual
cmtObservedThreeBIncrementMatchesResidual = refl

rawTateQ3DepthIsNotCMTIncrement :
  ordinaryFirstU3VisibleDepth
  ≡ cmtObservedThreeBIncrement
  ->
  ⊥
rawTateQ3DepthIsNotCMTIncrement ()

------------------------------------------------------------------------
-- 6. Mechanism firewalls.
------------------------------------------------------------------------

data RawTateCoefficientDepthIsExceptionalFourthTerm : Set where
data DisplayedPrefixProvesAllCoefficientValuations : Set where
data CMTObservedIncrementIsTateCoefficientDepth : Set where
data BorcherdsCreditedWithMonsterResidualTwo : Set where
data CarnahanCreditedWithBadLevelIgusaLocalization : Set where

rawTateCoefficientDepthIsNotFourthTerm :
  RawTateCoefficientDepthIsExceptionalFourthTerm -> ⊥
rawTateCoefficientDepthIsNotFourthTerm ()

displayedPrefixDoesNotProveAllCoefficientValuations :
  DisplayedPrefixProvesAllCoefficientValuations -> ⊥
displayedPrefixDoesNotProveAllCoefficientValuations ()

cmtIncrementIsNotRawTateCoefficientDepth :
  CMTObservedIncrementIsTateCoefficientDepth -> ⊥
cmtIncrementIsNotRawTateCoefficientDepth ()

borcherdsNotCreditedWithResidualTwo :
  BorcherdsCreditedWithMonsterResidualTwo -> ⊥
borcherdsNotCreditedWithResidualTwo ()

carnahanNotCreditedWithIgusaLocalization :
  CarnahanCreditedWithBadLevelIgusaLocalization -> ⊥
carnahanNotCreditedWithIgusaLocalization ()

------------------------------------------------------------------------
-- 7. Live boundary.
------------------------------------------------------------------------

integralTateBoundary :
  Tate.PBIntegralTateBridgeBoundary
integralTateBoundary =
  Tate.canonicalPBIntegralTateBridgeBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record ThreeBIntegralTateTraceValuationAuditBoundary : Set where
  constructor threeB-integral-tate-trace-valuation-audit-boundary
  field
    borcherdsThreeBCompanionSixBSourced : Bool
    threeBHauptmodulPrefixSourced : Bool
    sixBHauptmodulPrefixSourced : Bool
    ordinaryTatePrefixSourced : Bool
    superTatePrefixSourced : Bool
    integralTateInterpretationSourced : Bool
    displayedPrefixThreeAdicDepthsAudited : Bool
    ordinaryFirstU3DepthOne : Bool
    superFirstU3DepthOne : Bool
    rawFirstU3DepthMatchesResidualTwo : Bool
    cmtEventualIncrementTwoRecorded : Bool
    cmtIncrementDistinguishedFromRawCoefficientDepth : Bool
    displayedPrefixPromotedToAllSeriesTheorem : Bool
    attributionFirewallPreserved : Bool

canonicalThreeBIntegralTateTraceValuationAuditBoundary :
  ThreeBIntegralTateTraceValuationAuditBoundary
canonicalThreeBIntegralTateTraceValuationAuditBoundary =
  threeB-integral-tate-trace-valuation-audit-boundary
    true true true true true true true true true false true true false true
