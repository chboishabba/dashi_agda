{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98BidiWallRound191Exact where

------------------------------------------------------------------------
-- ROUND191 BIDI WALL AUDIT
--
-- Push both current fronts until they meet an actual type-level boundary.
-- This module deliberately does not convert status Bools or a side-four test
-- carrier into theorem evidence for a different ambient lattice.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierRound187Exact as R187
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierErasureBridgeExact as Erase
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.Closure.YMSprint129SpectralGapTransportClosure as S129
import DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation as ClayObligation

-- Source-side success already owned: the selected side-four physical background
-- has an exact unit-quaternion periodic realization, and erasure preserves its
-- path product.
sideFourSelectedPhysicalRealization :
  Physical.RationalSU2Background4 →
  Bond.PeriodicBondGaugeRealization
    3 SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
sideFourSelectedPhysicalRealization = R187.physicalBackgroundRealization

sourcePathErasureHomomorphismOwned : ProofLevel
sourcePathErasureHomomorphismOwned =
  Erase.cmp98SelectedPhysicalPathErasureLevel

-- Terminal-side facts literally available at the two owners.
sprint129MassGapStatusTrue :
  S129.continuumMassGapProvedHere ≡ true
sprint129MassGapStatusTrue = S129.continuumMassGapProvedHereIsTrue

paper7ClayCompositionStillFalse :
  ClayObligation.internalClayCompositionConstructed
    ClayObligation.canonicalPaper7CompositionDependencyReceipt
  ≡ false
paper7ClayCompositionStillFalse =
  ClayObligation.internalClayCompositionConstructedIsFalse
    ClayObligation.canonicalPaper7CompositionDependencyReceipt

-- BIDI WALL A:
-- `sideFourSelectedPhysicalRealization` is literally indexed by n = 3
-- (period side suc 3 = 4).  CMP98 Eq.(119)'s path compiler is generic in n.
-- The repository search performed for this round found no generic physical
-- `RationalSU2Background n` whose selected variational bridge is already
-- instantiated on arbitrary `PositiveBond (suc n)`.  Consequently R187 must
-- not be silently used as the arbitrary-n physical producer.
literalArbitraryPeriodicSelectedBackgroundProducerRound191Level : ProofLevel
literalArbitraryPeriodicSelectedBackgroundProducerRound191Level = conditional

-- BIDI WALL B:
-- Sprint129's true status bit is not an inhabitant of the theorem-shaped
-- Paper-7/Clay obligations.  The canonical Paper-7 composition remains false.
-- The next terminal move must find or construct explicit theorem inhabitants
-- for the selected obligation fields, or a later theorem-bearing owner that
-- supersedes them by same-object transport.
literalTerminalClayCompositionTheoremRound191Level : ProofLevel
literalTerminalClayCompositionTheoremRound191Level = conditional

cmp98BidiWallAuditRound191Level : ProofLevel
cmp98BidiWallAuditRound191Level = machineChecked
