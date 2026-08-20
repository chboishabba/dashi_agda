module DASHI.Arithmetic.VpDepthStrictMinimumBridgeExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE BRIDGE: bounded integer p-depth -> generic strict-minimum core
--
-- This module deliberately does NOT identify the bounded Nat valuation with
-- Dwork's p-adic analytic valuation.  It reuses the already-constructive
-- `vp-depth-add-min-unequal` theorem as an executable integer model of the
-- same non-Archimedean algebra consumed by
-- `SeparatedLeadingValuationExact`.
--
-- The point is architectural:
--
--   Dwork analytic source authority
--       -> genuine p-adic carrier / valuation
--
-- and independently
--
--   VpDepth executable Nat carrier
--       -> same strict-minimum theorem shape.
--
-- Thus downstream leading-term proofs share ONE algebraic interface without
-- promoting a fuel-bounded integer depth computation into p-adic analysis.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Arithmetic.VpDepth as Depth
import DASHI.Algebra.SeparatedLeadingValuationExact as Leading

------------------------------------------------------------------------
-- Small Nat lemmas kept local so this bridge does not depend on theorem-name
-- choices elsewhere in the stdlib.
------------------------------------------------------------------------

ltIrreflLocal : (n : Nat) -> ¬ (n < n)
ltIrreflLocal zero ()
ltIrreflLocal (suc n) (s≤s h) = ltIrreflLocal n h

ltImpliesNeq : {m n : Nat} -> m < n -> m ≡ n -> ⊥
ltImpliesNeq h refl = ltIrreflLocal _ h

minNatLeftOfStrictLess : {m n : Nat} -> m < n -> Depth.minNat m n ≡ m
minNatLeftOfStrictLess {zero} {zero} ()
minNatLeftOfStrictLess {zero} {suc n} h = refl
minNatLeftOfStrictLess {suc m} {zero} ()
minNatLeftOfStrictLess {suc m} {suc n} (s≤s h) =
  cong suc (minNatLeftOfStrictLess h)

------------------------------------------------------------------------
-- Fixed-fuel bounded strict-minimum valuation.
------------------------------------------------------------------------

boundedVpStrictMinimum : (fuel p : Nat) -> Leading.StrictMinimumValuation Nat
boundedVpStrictMinimum fuel p = record
  { Leading.add = _+_
  ; Leading.valuation = Depth.vp-depth fuel p
  ; Leading.strictMinimumLaw = strictMinimum
  }
  where
    strictMinimum :
      (x y : Nat) ->
      Depth.vp-depth fuel p x < Depth.vp-depth fuel p y ->
      Depth.vp-depth fuel p (x + y) ≡ Depth.vp-depth fuel p x
    strictMinimum x y depthLt =
      trans
        (Depth.vp-depth-add-min-unequal
          fuel p x y (ltImpliesNeq depthLt))
        (minNatLeftOfStrictLess depthLt)

------------------------------------------------------------------------
-- Reusable exact leading-term consequence on the executable integer shadow.
------------------------------------------------------------------------

boundedSeparatedLeadingDeterminesDepth :
  (fuel p total : Nat) ->
  (S : Leading.SeparatedLeadingTerm (boundedVpStrictMinimum fuel p) total) ->
  Leading.valuation (boundedVpStrictMinimum fuel p) total
  ≡ Leading.valuation (boundedVpStrictMinimum fuel p) (Leading.leading S)
boundedSeparatedLeadingDeterminesDepth fuel p total S =
  Leading.separatedLeadingDeterminesValuation
    (boundedVpStrictMinimum fuel p) total S

record VpDepthStrictMinimumBridgeBoundary : Set where
  field
    boundedVpDepthReused : Bool
    unequalAdditionTheoremReused : Bool
    strictMinimumInterfaceConstructed : Bool
    executableLeadingTermShadowConstructed : Bool
    fuelAdequacyPostulateConsumed : Bool
    boundedNatDepthIdentifiedWithDworkPadicValuation : Bool

canonicalVpDepthStrictMinimumBridgeBoundary : VpDepthStrictMinimumBridgeBoundary
canonicalVpDepthStrictMinimumBridgeBoundary = record
  { boundedVpDepthReused = true
  ; unequalAdditionTheoremReused = true
  ; strictMinimumInterfaceConstructed = true
  ; executableLeadingTermShadowConstructed = true
  ; fuelAdequacyPostulateConsumed = false
  ; boundedNatDepthIdentifiedWithDworkPadicValuation = false
  }
