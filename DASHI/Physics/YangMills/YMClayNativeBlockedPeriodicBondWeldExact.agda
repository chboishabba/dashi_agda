module DASHI.Physics.YangMills.YMClayNativeBlockedPeriodicBondWeldExact where

------------------------------------------------------------------------
-- R445: original positive bonds at side M*L -> original Balaban blocks.
--
-- Existing BalabanBlockedPeriodicLattice proves the Fin-based cube
-- decomposition (fine size M*L) == (coarse size M, offset size L).
-- The actual R443/R445 Wilson/Gibbs source is the separate
-- CyclicIndex-based BalabanPeriodicTorus4Carrier.
--
-- This module composes their exact codecs through the source-written
-- CyclicIndex/Fin isomorphism. The resulting two-way maps are on the
-- ORIGINAL physical four-torus sites and positive-bond labels.
-- It does not invent a new scalar, gauge field, coupling or measure.
--
-- NOT YET: a link-valued coarse-graining map, gauge transport of each
-- coarse edge, Wilson action blocking identity, beta(a) identification,
-- normalized measure disintegration or scale-uniform bounds.
-- Existing Bałaban/P06 and DASHI theorem owners retain attribution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry as Cube
import DASHI.Physics.YangMills.BalabanBlockedPeriodicLattice as Block
import DASHI.Physics.YangMills.YMClayNativeCyclicFinIsoSafeExact as Iso

siteToCube :
  ∀ {N} → Torus.periodicTorus4Definition N → Cube.Cube4 N
siteToCube (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) =
  Cube.cube4
    (Iso.cyclicToFin x0) (Iso.cyclicToFin x1)
    (Iso.cyclicToFin x2) (Iso.cyclicToFin x3)

cubeToSite :
  ∀ {N} → Cube.Cube4 N → Torus.periodicTorus4Definition N
cubeToSite (Cube.cube4 x0 x1 x2 x3) =
  Torus.pair
    (Torus.pair (Iso.finToCyclic x0) (Iso.finToCyclic x1))
    (Torus.pair (Iso.finToCyclic x2) (Iso.finToCyclic x3))

siteCubeRoundtrip :
  ∀ {N} (site : Torus.periodicTorus4Definition N) →
  cubeToSite (siteToCube site) ≡ site
siteCubeRoundtrip
    (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  rewrite Iso.cyclicRoundtrip x0
        | Iso.cyclicRoundtrip x1
        | Iso.cyclicRoundtrip x2
        | Iso.cyclicRoundtrip x3 = refl

cubeSiteRoundtrip :
  ∀ {N} (site : Cube.Cube4 N) →
  siteToCube (cubeToSite site) ≡ site
cubeSiteRoundtrip (Cube.cube4 x0 x1 x2 x3)
  rewrite Iso.finRoundtrip x0
        | Iso.finRoundtrip x1
        | Iso.finRoundtrip x2
        | Iso.finRoundtrip x3 = refl

blockNativeSite :
  (M L : Nat) →
  Torus.periodicTorus4Definition (M * L) →
  Block.BlockedCube4 M L
blockNativeSite M L fine =
  Block.splitFinePoint {M = M} {L = L} (siteToCube fine)

unblockNativeSite :
  (M L : Nat) →
  Block.BlockedCube4 M L →
  Torus.periodicTorus4Definition (M * L)
unblockNativeSite M L blocked =
  cubeToSite (Block.finePoint {M = M} {L = L} blocked)

blockNativeSiteAfterUnblock :
  ∀ M L (blocked : Block.BlockedCube4 M L) →
  blockNativeSite M L (unblockNativeSite M L blocked) ≡ blocked
blockNativeSiteAfterUnblock M L blocked =
  trans
    (cong (Block.splitFinePoint {M = M} {L = L})
      (cubeSiteRoundtrip
        (Block.finePoint {M = M} {L = L} blocked)))
    (Block.splitFinePointFinePoint {M = M} {L = L} blocked)

unblockNativeSiteAfterBlock :
  ∀ M L (site : Torus.periodicTorus4Definition (M * L)) →
  unblockNativeSite M L (blockNativeSite M L site) ≡ site
unblockNativeSiteAfterBlock M L site =
  trans
    (cong cubeToSite
      (Block.finePointSplitFinePoint {M = M} {L = L}
        (siteToCube site)))
    (siteCubeRoundtrip site)

BlockedPositiveBond : (M L : Nat) → Set
BlockedPositiveBond M L =
  Torus.Product (Block.BlockedCube4 M L) Torus.Axis4

blockNativeBond :
  (M L : Nat) →
  Torus.PositiveBond (M * L) →
  BlockedPositiveBond M L
blockNativeBond M L (Torus.pair site axis) =
  Torus.pair (blockNativeSite M L site) axis

unblockNativeBond :
  (M L : Nat) →
  BlockedPositiveBond M L →
  Torus.PositiveBond (M * L)
unblockNativeBond M L (Torus.pair blocked axis) =
  Torus.pair (unblockNativeSite M L blocked) axis

blockNativeBondAfterUnblock :
  ∀ M L (bond : BlockedPositiveBond M L) →
  blockNativeBond M L (unblockNativeBond M L bond) ≡ bond
blockNativeBondAfterUnblock M L (Torus.pair blocked axis) =
  cong (λ site → Torus.pair site axis)
    (blockNativeSiteAfterUnblock M L blocked)

unblockNativeBondAfterBlock :
  ∀ M L (bond : Torus.PositiveBond (M * L)) →
  unblockNativeBond M L (blockNativeBond M L bond) ≡ bond
unblockNativeBondAfterBlock M L (Torus.pair site axis) =
  cong (λ selected → Torus.pair selected axis)
    (unblockNativeSiteAfterBlock M L site)
