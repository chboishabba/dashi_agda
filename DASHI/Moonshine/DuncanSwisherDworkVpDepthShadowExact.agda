module DASHI.Moonshine.DuncanSwisherDworkVpDepthShadowExact where

------------------------------------------------------------------------
-- EXECUTABLE INTEGER SHADOW OF THE DWORK EXCEPTIONAL LEADING-TERM STEP
--
-- This module is intentionally NOT a source theorem about Dwork's analytic
-- functions.  It cross-pollinates the existing constructive integer valuation
-- infrastructure into the generic strict-minimum algebra already used by
-- `DuncanSwisherDworkExceptionalPartialFractionSharpnessExact`.
--
-- For the three exceptional primes, use literal integer representatives with
-- the same depth separation pattern:
--
--   p=5:   125 = 5^3,   625 = 5^4,   750 = 125 + 625;
--   p=7:    49 = 7^2,   343 = 7^3,   392 =  49 + 343;
--   p=11:  121 =11^2,  1331 =11^3,  1452 = 121 +1331.
--
-- The bounded executable valuation verifies the strict separation and the
-- generic strict-minimum theorem derives total depths 3,2,2.
--
-- NO claim is made that these Nat values are A1, J-alpha or the Dwork
-- remainder.  They are a regression that the lower-level valuation calculus
-- and the abstract non-Archimedean leading-term core now share one interface.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Arithmetic.VpDepthStrictMinimumBridgeExact as VpBridge
import DASHI.Algebra.SeparatedLeadingValuationExact as Leading

------------------------------------------------------------------------
-- One fuel comfortably beyond all displayed depths.
------------------------------------------------------------------------

shadowFuel : Nat
shadowFuel = 8

p5Valuation : Leading.StrictMinimumValuation Nat
p5Valuation = VpBridge.boundedVpStrictMinimum shadowFuel 5

p7Valuation : Leading.StrictMinimumValuation Nat
p7Valuation = VpBridge.boundedVpStrictMinimum shadowFuel 7

p11Valuation : Leading.StrictMinimumValuation Nat
p11Valuation = VpBridge.boundedVpStrictMinimum shadowFuel 11

------------------------------------------------------------------------
-- p=5 shadow: 3 < 4, hence the sum has depth 3.
------------------------------------------------------------------------

p5LeadingDepth : Leading.valuation p5Valuation 125 ≡ 3
p5LeadingDepth = refl

p5RemainderDepth : Leading.valuation p5Valuation 625 ≡ 4
p5RemainderDepth = refl

p5TotalDepth : Leading.valuation p5Valuation 750 ≡ 3
p5TotalDepth =
  trans
    (Leading.strictMinimumLaw p5Valuation 125 625 ≤-refl)
    p5LeadingDepth

------------------------------------------------------------------------
-- p=7 shadow: 2 < 3, hence the sum has depth 2.
------------------------------------------------------------------------

p7LeadingDepth : Leading.valuation p7Valuation 49 ≡ 2
p7LeadingDepth = refl

p7RemainderDepth : Leading.valuation p7Valuation 343 ≡ 3
p7RemainderDepth = refl

p7TotalDepth : Leading.valuation p7Valuation 392 ≡ 2
p7TotalDepth =
  trans
    (Leading.strictMinimumLaw p7Valuation 49 343 ≤-refl)
    p7LeadingDepth

------------------------------------------------------------------------
-- p=11 shadow: 2 < 3, hence the sum has depth 2.
------------------------------------------------------------------------

p11LeadingDepth : Leading.valuation p11Valuation 121 ≡ 2
p11LeadingDepth = refl

p11RemainderDepth : Leading.valuation p11Valuation 1331 ≡ 3
p11RemainderDepth = refl

p11TotalDepth : Leading.valuation p11Valuation 1452 ≡ 2
p11TotalDepth =
  trans
    (Leading.strictMinimumLaw p11Valuation 121 1331 ≤-refl)
    p11LeadingDepth

record DuncanSwisherDworkVpDepthShadowBoundary : Set where
  field
    boundedIntegerValuationReused : Bool
    genericStrictMinimumCoreReused : Bool
    exceptionalDepthPatternExecutable : Bool
    p5ThreeDerived : Bool
    p7TwoDerived : Bool
    p11TwoDerived : Bool
    DworkPadicCarrierConstructedHere : Bool
    integerShadowIdentifiedWithA1OrJ : Bool
    VpTrueGlobalAdequacyPostulateConsumed : Bool

canonicalDuncanSwisherDworkVpDepthShadowBoundary :
  DuncanSwisherDworkVpDepthShadowBoundary
canonicalDuncanSwisherDworkVpDepthShadowBoundary = record
  { boundedIntegerValuationReused = true
  ; genericStrictMinimumCoreReused = true
  ; exceptionalDepthPatternExecutable = true
  ; p5ThreeDerived = true
  ; p7TwoDerived = true
  ; p11TwoDerived = true
  ; DworkPadicCarrierConstructedHere = false
  ; integerShadowIdentifiedWithA1OrJ = false
  ; VpTrueGlobalAdequacyPostulateConsumed = false
  }
