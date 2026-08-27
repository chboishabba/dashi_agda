module DASHI.Physics.Closure.TSFVBidirectionalActionRealizationObligationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.BidirectionalAdmissibleActionRealizationExact as Realize
import DASHI.Physics.Closure.TSFVBidirectionalCausticBridgeExact as BidiBridge
import DASHI.Physics.Closure.TSFVNonseparableTransitionKernelExact as Kernel

------------------------------------------------------------------------
-- The next upstream bridge is not allowed to be an arbitrary encoding.
--
-- We now possess:
--   * a concrete two-boundary History3 fibre, and
--   * a structural T-invariant nonseparable Candidate256 transition kernel.
--
-- What is still missing is a justified physical identification of histories
-- in the first carrier with transition traces in the second carrier.
------------------------------------------------------------------------

data TSFVHistoryRealizationAuthority : Set where
  -- Intentionally no constructor.  A later physical/source-backed tranche must
  -- supply an authority/receipt before the carriers may be identified.

record TSFVBidirectionalActionRealization : Set₁ where
  field
    authority : TSFVHistoryRealizationAuthority

    realization :
      Realize.BidirectionalActionRealization
        BidiBridge.historyBidirectionalSurface
        Kernel.transitionLocalActionSystem

    realizationBoundary :
      Realize.BidirectionalActionRealizationBoundary

    physicalIdentificationReading : String

open TSFVBidirectionalActionRealization public

data TSFVBidirectionalActionRealizationStatus : Set where
  historyAndKernelConstructedRealizationAuthorityMissing :
    TSFVBidirectionalActionRealizationStatus

currentTSFVBidirectionalActionRealizationStatus :
  TSFVBidirectionalActionRealizationStatus
currentTSFVBidirectionalActionRealizationStatus =
  historyAndKernelConstructedRealizationAuthorityMissing

record TSFVBidirectionalActionRealizationBoundary : Set where
  constructor tsfvBidirectionalActionRealizationBoundary
  field
    bidiHistoryFibreConstructed : Bool
    bidiHistoryFibreConstructedIsTrue :
      bidiHistoryFibreConstructed ≡ true

    nonseparableTransitionKernelConstructed : Bool
    nonseparableTransitionKernelConstructedIsTrue :
      nonseparableTransitionKernelConstructed ≡ true

    justifiedCarrierRealizationConstructed : Bool
    justifiedCarrierRealizationConstructedIsFalse :
      justifiedCarrierRealizationConstructed ≡ false

    arbitraryHistoryEncodingClosesPhysicalAdmissibility : Bool
    arbitraryHistoryEncodingClosesPhysicalAdmissibilityIsFalse :
      arbitraryHistoryEncodingClosesPhysicalAdmissibility ≡ false

canonicalTSFVBidirectionalActionRealizationBoundary :
  TSFVBidirectionalActionRealizationBoundary
canonicalTSFVBidirectionalActionRealizationBoundary =
  tsfvBidirectionalActionRealizationBoundary
    true refl
    true refl
    false refl
    false refl
