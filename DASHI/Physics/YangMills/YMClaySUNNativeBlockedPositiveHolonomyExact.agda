module DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact where

------------------------------------------------------------------------
-- R445 selected SU(N) same-object adapter to the genuine ordered
-- group-valued M×L positive-link block field, WITHOUT a second link model.
--
-- The generic constructive positive path/gauge theorem is owned by
-- YMClayNativeBlockedPositiveHolonomyGaugeExact; it uses the original
-- finite 4-torus positive bond carrier and the existing Bond group laws.
--
-- This module chooses EXACTLY:
--   - SUN.CertifiedSUNMatrixTheory N Matrix Complex and its real link;
--   - Native.sunExactSignedLinkGroup theory (selected original group);
--   - Variable.SUNPeriodicLinks theory n and SUNPeriodicGauge theory n;
--   - Variable.periodicSUNGaugeTransform on the original fine/coarse
--     Wilson links, and the original selected signed path realization.
--
-- Finite source result: actual SU(N) blocked links and gauge covariance
-- at the computed fine endpoint, plus conditional exact coarse-source
-- covariance if the remaining periodic modular block-endpoint equation
-- is constructed. The endpoint equation has NO Haar/real/OS inputs.
--
-- No Gibbs measure pushforward, block Wilson equality or uniform mass gap.
-- Wilson/Bałaban and existing DASHI source owners retain attribution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact as Block

module _
    {Matrix Complex : Set} {N m l : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  selectedGroup : Bond.ExactLinkGroup Link
  selectedGroup = Native.sunExactSignedLinkGroup theory

  FineTail : Nat
  FineTail = l + m * suc l

  FineLinks : Set
  FineLinks = Variable.SUNPeriodicLinks theory FineTail

  CoarseLinks : Set
  CoarseLinks = Variable.SUNPeriodicLinks theory m

  FineGauge : Set
  FineGauge = Variable.SUNPeriodicGauge theory FineTail

  CoarseGauge : Set
  CoarseGauge = Variable.SUNPeriodicGauge theory m

  nativeSUNBlockLinks : FineLinks → CoarseLinks
  nativeSUNBlockLinks =
    Block.nativeBlockedPositiveLinks selectedGroup

  nativeSUNBlockGauge : FineGauge → CoarseGauge
  nativeSUNBlockGauge =
    Block.nativeBlockedCoarseGauge selectedGroup

  nativeSUNBlockAgreesSelectedPath :
    ∀ (fine : FineLinks) (gamma : FineGauge) site axis →
    nativeSUNBlockLinks fine (Torus.pair site axis)
    ≡
    Bond.pathHolonomy
      (Variable.periodicSUNRealization theory FineTail fine gamma)
      (Block.fineBlockOrigin selectedGroup site)
      (Block.positiveBlockDirections selectedGroup axis)
  nativeSUNBlockAgreesSelectedPath fine gamma site axis =
    Block.positiveHolonomyIsSelectedPath selectedGroup
      (Variable.periodicSUNRealization theory FineTail fine gamma)
      (Block.fineBlockOrigin selectedGroup site) axis (suc l)

  nativeSUNBlockGaugeLawAtFineEndpoint :
    ∀ (fine : FineLinks) (gamma : FineGauge) site axis →
    nativeSUNBlockLinks
      (Variable.periodicSUNGaugeTransform
        theory FineTail fine gamma)
      (Torus.pair site axis)
    ≡
    Bond.multiply selectedGroup
      (Bond.multiply selectedGroup
        (nativeSUNBlockGauge gamma site)
        (nativeSUNBlockLinks fine (Torus.pair site axis)))
      (Bond.inverse selectedGroup
        (gamma
          (Block.positiveSteps
            (Block.fineBlockOrigin selectedGroup site)
            axis (suc l))))
  nativeSUNBlockGaugeLawAtFineEndpoint fine gamma site axis =
    Block.nativeBlockedGaugeLawAtFineEndpoint
      selectedGroup fine gamma site axis

  -- The remaining single finite-arithmetic original-source obligation:
  -- repeated positive cyclic successor on the selected fine block origin
  -- equals the selected next coarse block origin (periodic wrap included).
  NativeSUNBlockEndpoint : Set
  NativeSUNBlockEndpoint =
    Block.BlockEndpointCompatibility selectedGroup

  nativeSUNBlockGaugeLawOnCoarse :
    NativeSUNBlockEndpoint →
    ∀ (fine : FineLinks) (gamma : FineGauge)
      (bond : Torus.PositiveBond (suc m)) →
    nativeSUNBlockLinks
      (Variable.periodicSUNGaugeTransform
        theory FineTail fine gamma) bond
    ≡
    Variable.periodicSUNGaugeTransform theory m
      (nativeSUNBlockLinks fine)
      (nativeSUNBlockGauge gamma) bond
  nativeSUNBlockGaugeLawOnCoarse endpoint fine gamma bond =
    Block.nativeBlockedGaugeLawOnCoarse selectedGroup
      endpoint fine gamma bond
