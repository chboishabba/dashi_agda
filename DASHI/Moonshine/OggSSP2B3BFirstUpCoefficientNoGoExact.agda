module DASHI.Moonshine.OggSSP2B3BFirstUpCoefficientNoGoExact where

------------------------------------------------------------------------
-- 2B / 3B FIRST U_p-COEFFICIENT VALUATION NO-GO
--
-- SOURCE INPUT
--
-- Standard McKay--Thompson q-expansions:
--
--   T_2B = q^-1 + 276 q - 2048 q^2 + 11202 q^3 - ...,
--   T_3B = q^-1 +  54 q -   76 q^2 -   243 q^3 + ....
--
-- Applying U_p sends the coefficient a(p n) to the q^n slot.  Thus the first
-- positive q coefficient after one U_p step is:
--
--   p=2 : a_2 = -2048 = -2^11,
--   p=3 : a_3 =  -243 = -3^5.
--
-- Those valuations 11 and 5 are NOT the independent local-centralizer defects
-- 10 and 2.
--
-- CONSEQUENCE
--
-- Ordinary one-step U_p leading-coefficient valuation is not the exceptional
-- fourth term.  The missing extraction must use a stronger bad-level /
-- twisted-local normalization or a different derived q-expansion observable.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP2B3BPadicHauptmodulBridgeExact as Padic
import DASHI.Moonshine.OggSSPSmallPrimeMonsterLocalCentralizerValuationExact as Local
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Sourced first U_p positive coefficients.
------------------------------------------------------------------------

p2FirstUpPositiveCoefficientMagnitude : Nat
p2FirstUpPositiveCoefficientMagnitude = 2048

p3FirstUpPositiveCoefficientMagnitude : Nat
p3FirstUpPositiveCoefficientMagnitude = 243

p2FirstUpValuation : Nat
p2FirstUpValuation = 11

p3FirstUpValuation : Nat
p3FirstUpValuation = 5

p2CoefficientIsTwoToEleven :
  p2FirstUpPositiveCoefficientMagnitude ≡ 2048
p2CoefficientIsTwoToEleven = refl

p3CoefficientIsThreeToFive :
  p3FirstUpPositiveCoefficientMagnitude ≡ 243
p3CoefficientIsThreeToFive = refl

------------------------------------------------------------------------
-- 2. Exact mismatch with the independently defined Monster-local defects.
------------------------------------------------------------------------

p2FirstUpValuationNotLocalDefect :
  p2FirstUpValuation ≡ Local.p2LocalCentralizerResidual -> ⊥
p2FirstUpValuationNotLocalDefect ()

p3FirstUpValuationNotLocalDefect :
  p3FirstUpValuation ≡ Local.p3LocalCentralizerResidual -> ⊥
p3FirstUpValuationNotLocalDefect ()

data FirstUpCoefficientValuationIsExceptionalFourthTerm : Set where
data PadicAnnihilationLeadingStepClosesMonsterBridge : Set where

firstUpCoefficientValuationIsNotFourthTerm :
  FirstUpCoefficientValuationIsExceptionalFourthTerm -> ⊥
firstUpCoefficientValuationIsNotFourthTerm ()

leadingUpStepDoesNotCloseMonsterBridge :
  PadicAnnihilationLeadingStepClosesMonsterBridge -> ⊥
leadingUpStepDoesNotCloseMonsterBridge ()

------------------------------------------------------------------------
-- 3. Retain the class-specific p-adic route.
------------------------------------------------------------------------

padicBridgeBoundary :
  Padic.ClassSpecificPadicHauptmodulBridgeBoundary
padicBridgeBoundary =
  Padic.canonicalClassSpecificPadicHauptmodulBridgeBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record FirstUpCoefficientNoGoBoundary : Set where
  constructor first-up-coefficient-no-go-boundary
  field
    class2BFirstUpCoefficientSourced : Bool
    class3BFirstUpCoefficientSourced : Bool
    p2FirstUpValuationEleven : Bool
    p3FirstUpValuationFive : Bool
    p2FirstUpMatchesLocalDefectTen : Bool
    p3FirstUpMatchesLocalDefectTwo : Bool
    ordinaryFirstUpShortcutRejected : Bool
    strongerPadicBadLevelExtractionStillRequired : Bool
    attributionFirewallPreserved : Bool

canonicalFirstUpCoefficientNoGoBoundary :
  FirstUpCoefficientNoGoBoundary
canonicalFirstUpCoefficientNoGoBoundary =
  first-up-coefficient-no-go-boundary
    true true true true false false true true true
