module DASHI.Physics.YangMills.YMClayR445NativePairHolonomyIdentityExact where

------------------------------------------------------------------------
-- P0.C ORIGINAL SOURCE: no alternate blocking map and no hypothetical
-- finite pair field. The *actual* native 4 -> 2 R445 positive bond
-- holonomy is the ordered product of its two original fine bonds.
--
-- Uses the existing Balaban native block-origin, selected original
-- periodic gauge bond carrier, and real certified SU(N) group laws.
-- This is pure finite geometry/group algebra; no fiber disintegration,
-- interacting RG decay or physical mass gap is claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact as Block
import DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact as SUNBlock

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  FineLinks : Set
  FineLinks = Variable.SUNPeriodicLinks theory 3

  CoarseBond : Set
  CoarseBond = Torus.PositiveBond 2

  originalGroup : Bond.ExactLinkGroup Link
  originalGroup = Native.sunExactSignedLinkGroup theory

  originalPairFirst : CoarseBond → Torus.PositiveBond 4
  originalPairFirst (Torus.pair site axis) =
    Torus.pair
      (Block.fineBlockOrigin {m = 1} {l = 1} originalGroup site)
      axis

  originalPairSecond : CoarseBond → Torus.PositiveBond 4
  originalPairSecond (Torus.pair site axis) =
    Torus.pair
      (Bond.positiveStep
        (Block.fineBlockOrigin {m = 1} {l = 1} originalGroup site)
        axis)
      axis

  originalPairedFineHolonomy : FineLinks → CoarseBond → Link
  originalPairedFineHolonomy fine bond =
    SUN.sunMultiply theory
      (fine (originalPairFirst bond))
      (fine (originalPairSecond bond))

  originalR445NativeBlockAgreesPairedCodec :
    (fine : FineLinks) (bond : CoarseBond) →
    SUNBlock.nativeSUNBlockLinks {m = 1} {l = 1}
      theory fine bond
    ≡ originalPairedFineHolonomy fine bond
  originalR445NativeBlockAgreesPairedCodec
    fine (Torus.pair site axis) =
    cong
      (SUN.sunMultiply theory
        (fine (Torus.pair
          (Block.fineBlockOrigin {m = 1} {l = 1}
            originalGroup site)
          axis)))
      (Bond.identityRight originalGroup
        (fine (Torus.pair
          (Bond.positiveStep
            (Block.fineBlockOrigin {m = 1} {l = 1}
              originalGroup site)
            axis)
          axis)))

  -- P0.A is a separate, unproved injectivity theorem on the TWO
  -- actual source bond selectors. This is the exact next input to
  -- construct the R445 64-pair/896-residual vector permutation;
  -- P0.C does NOT assume that property.
