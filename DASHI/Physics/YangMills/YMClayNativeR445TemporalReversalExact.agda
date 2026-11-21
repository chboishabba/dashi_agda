module DASHI.Physics.YangMills.YMClayNativeR445TemporalReversalExact where

------------------------------------------------------------------------
-- YM M.04: ORIGINAL native non-Abelian two-link temporal reversal.
-- A physical site-plane theta reverses the ordered two fine segments
-- and takes their inverses. The result is the INVERSE of the actual
-- R445 coarse holonomy, not its un-reversed/inverted surrogate.
-- This is an exact native group proof; the torus reflection-site
-- indexing and positive-time support preservation are separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact as Block
import DASHI.Physics.YangMills.YMClayNativeSideFourTwoLinkPairSameObjectExact as Pair
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Wilson

module _ {Value : Set} (group : Bond.ExactLinkGroup Value) where

  originalNativeReversedTwoLinkIsInverseBlock :
    (fine : Bond.PeriodicBondField 3 Value)
    (coarse : Torus.PositiveBond 2) →
    Bond.multiply group
      (Bond.inverse group
        (fine (Pair.originalSecondFineBond group coarse)))
      (Bond.inverse group
        (fine (Pair.originalFirstFineBond group coarse)))
    ≡
    Bond.inverse group
      (Block.nativeBlockedPositiveLinks {m = 1} {l = 1}
        group fine coarse)
  originalNativeReversedTwoLinkIsInverseBlock fine coarse =
    trans
      (sym (Bond.inverseProduct group
        (fine (Pair.originalFirstFineBond group coarse))
        (fine (Pair.originalSecondFineBond group coarse))))
      (sym (cong (Bond.inverse group)
        (Pair.originalNativeBlockedLinkIsLiteralTwoFineProduct
          group fine coarse)))

-- Actual original compact-group SU(N) link carrier, no toy group in proof.
module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  sourceGroup : Bond.ExactLinkGroup (SUN.SUNMatrixElement theory)
  sourceGroup = Native.sunExactSignedLinkGroup theory

  originalSUNTimeReversalTwoLink :
    (fine : Wilson.SUNPeriodicLinks theory 3)
    (coarse : Torus.PositiveBond 2) →
    Bond.multiply sourceGroup
      (Bond.inverse sourceGroup
        (fine (Pair.originalSecondFineBond sourceGroup coarse)))
      (Bond.inverse sourceGroup
        (fine (Pair.originalFirstFineBond sourceGroup coarse)))
    ≡
    Bond.inverse sourceGroup
      (Block.nativeBlockedPositiveLinks {m = 1} {l = 1}
        sourceGroup fine coarse)
  originalSUNTimeReversalTwoLink =
    originalNativeReversedTwoLinkIsInverseBlock sourceGroup
