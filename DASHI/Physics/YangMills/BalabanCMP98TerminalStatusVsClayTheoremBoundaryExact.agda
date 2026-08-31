{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98TerminalStatusVsClayTheoremBoundaryExact where

------------------------------------------------------------------------
-- TERMINAL BIDI AUTHORITY CORRECTION
--
-- Sprint129 records project/evidence closure flags.  The canonical continuum
-- Clay mass-gap owner still exposes theorem-shaped obligations and explicitly
-- records internal Clay composition as unconstructed.  A Boolean status flag
-- cannot inhabit one of those obligation types by `refl`.
--
-- This file makes that distinction available to the Eq.(119) BIDI lane without
-- negating or rewriting either historical owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.YMSprint129SpectralGapTransportClosure as S129
import DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation as ClayObligation

-- What Sprint129 literally proves at this surface: equality of a declared Bool
-- with `true`.
sprint129ContinuumMassGapStatusIsTrue :
  S129.continuumMassGapProvedHere ≡ true
sprint129ContinuumMassGapStatusIsTrue =
  S129.continuumMassGapProvedHereIsTrue

-- What the canonical Clay obligation literally records at its own surface:
-- the internal composition is still false.
clayInternalCompositionStillUnconstructed :
  ClayObligation.internalClayCompositionConstructed
    ClayObligation.canonicalPaper7CompositionDependencyReceipt
  ≡ false
clayInternalCompositionStillUnconstructed =
  ClayObligation.internalClayCompositionConstructedIsFalse
    ClayObligation.canonicalPaper7CompositionDependencyReceipt

-- Package the actual authority split rather than silently coercing a status
-- equality into a theorem receipt.
record TerminalStatusTheoremAuthorityBoundary : Set where
  field
    sprint129Status : S129.continuumMassGapProvedHere ≡ true

    clayCompositionStatus :
      ClayObligation.internalClayCompositionConstructed
        ClayObligation.canonicalPaper7CompositionDependencyReceipt
      ≡ false

open TerminalStatusTheoremAuthorityBoundary public

canonicalTerminalStatusTheoremAuthorityBoundary :
  TerminalStatusTheoremAuthorityBoundary
canonicalTerminalStatusTheoremAuthorityBoundary = record
  { sprint129Status = sprint129ContinuumMassGapStatusIsTrue
  ; clayCompositionStatus = clayInternalCompositionStillUnconstructed
  }

-- The canonical theorem-bearing endpoint is therefore not the Sprint129 Bool.
-- Any promotion route must explicitly inhabit/bridge the obligation fields
-- selected by `ContinuumClayMassGapAbstractObligationFields` or a newer literal
-- theorem consumer that supersedes that owner by construction.
terminalSprintStatusDoesNotByItselfConstructClayCompositionLevel : ProofLevel
terminalSprintStatusDoesNotByItselfConstructClayCompositionLevel = machineChecked

literalTerminalClayTheoremBridgeLevel : ProofLevel
literalTerminalClayTheoremBridgeLevel = conditional
